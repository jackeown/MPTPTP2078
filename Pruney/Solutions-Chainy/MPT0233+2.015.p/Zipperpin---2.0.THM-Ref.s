%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOiUyvNTCe

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  214 ( 266 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X61: $i,X62: $i] :
      ( r1_tarski @ ( k1_tarski @ X61 ) @ ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r2_hidden @ X59 @ X60 )
      | ( ( k3_xboole_0 @ X60 @ ( k1_tarski @ X59 ) )
       != ( k1_tarski @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X23 )
      | ( X25 = X24 )
      | ( X25 = X21 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X21: $i,X24: $i,X25: $i] :
      ( ( X25 = X21 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ X25 @ ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOiUyvNTCe
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 323 iterations in 0.147s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.43/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(t28_zfmisc_1, conjecture,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.43/0.60          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.43/0.60             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.43/0.60  thf('0', plain,
% 0.43/0.60      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t12_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      (![X61 : $i, X62 : $i]:
% 0.43/0.60         (r1_tarski @ (k1_tarski @ X61) @ (k2_tarski @ X61 @ X62))),
% 0.43/0.60      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.43/0.60  thf(t1_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.43/0.60       ( r1_tarski @ A @ C ) ))).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.60         (~ (r1_tarski @ X9 @ X10)
% 0.43/0.60          | ~ (r1_tarski @ X10 @ X11)
% 0.43/0.60          | (r1_tarski @ X9 @ X11))),
% 0.43/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.60  thf('3', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.43/0.60          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.43/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.43/0.60  thf(t28_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.60  thf('5', plain,
% 0.43/0.60      (![X14 : $i, X15 : $i]:
% 0.43/0.60         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.43/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.60  thf('6', plain,
% 0.43/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.43/0.60         = (k1_tarski @ sk_A))),
% 0.43/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.60  thf('7', plain,
% 0.43/0.60      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.60  thf(l29_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.43/0.60       ( r2_hidden @ B @ A ) ))).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      (![X59 : $i, X60 : $i]:
% 0.43/0.60         ((r2_hidden @ X59 @ X60)
% 0.43/0.60          | ((k3_xboole_0 @ X60 @ (k1_tarski @ X59)) != (k1_tarski @ X59)))),
% 0.43/0.60      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.43/0.60          | (r2_hidden @ X1 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.43/0.60        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.43/0.60  thf('11', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.43/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.43/0.60  thf(d2_tarski, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.43/0.60  thf('12', plain,
% 0.43/0.60      (![X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X25 @ X23)
% 0.43/0.60          | ((X25) = (X24))
% 0.43/0.60          | ((X25) = (X21))
% 0.43/0.60          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 0.43/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.43/0.60  thf('13', plain,
% 0.43/0.60      (![X21 : $i, X24 : $i, X25 : $i]:
% 0.43/0.60         (((X25) = (X21))
% 0.43/0.60          | ((X25) = (X24))
% 0.43/0.60          | ~ (r2_hidden @ X25 @ (k2_tarski @ X24 @ X21)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.43/0.60  thf('14', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D_1)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.43/0.60  thf('15', plain, (((sk_A) != (sk_D_1))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('16', plain, (((sk_A) != (sk_C))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('17', plain, ($false),
% 0.43/0.60      inference('simplify_reflect-', [status(thm)], ['14', '15', '16'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
