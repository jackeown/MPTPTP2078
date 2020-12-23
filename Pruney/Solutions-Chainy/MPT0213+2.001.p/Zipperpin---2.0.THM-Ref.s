%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNnhQdWZnh

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  96 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 ( 857 expanded)
%              Number of equality atoms :   23 (  76 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X14: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X10 ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( X1
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X10: $i,X14: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ( r2_hidden @ ( sk_C @ X14 @ X10 ) @ ( sk_D_1 @ X14 @ X10 ) )
      | ( r2_hidden @ ( sk_C @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('15',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('18',plain,(
    ! [X10: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ ( sk_C @ X14 @ X10 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNnhQdWZnh
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 38 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(t1_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('0', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf('1', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf(d4_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X10 : $i, X14 : $i]:
% 0.21/0.50         (((X14) = (k3_tarski @ X10))
% 0.21/0.50          | (r2_hidden @ (sk_D_1 @ X14 @ X10) @ X10)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X14 @ X10) @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.50  thf(d3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.50          | (r2_hidden @ X2 @ X4)
% 0.21/0.50          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.50         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.21/0.50          | ((X1) = (k3_tarski @ X0))
% 0.21/0.50          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D_1 @ X1 @ k1_xboole_0) @ X0)
% 0.21/0.50          | ((X1) = (k3_tarski @ k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X10 : $i, X14 : $i]:
% 0.21/0.50         (((X14) = (k3_tarski @ X10))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X14 @ X10) @ (sk_D_1 @ X14 @ X10))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X14 @ X10) @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.50  thf(antisymmetry_r2_hidden, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.21/0.51          | ((X1) = (k3_tarski @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (sk_C @ X1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.51          | ((X0) = (k3_tarski @ k1_xboole_0))
% 0.21/0.51          | ((X0) = (k3_tarski @ k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k3_tarski @ k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.51         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) = (k3_tarski @ k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '13'])).
% 0.21/0.51  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.51  thf('15', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]: (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]: (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X10 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (((X14) = (k3_tarski @ X10))
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X14 @ X10) @ X15)
% 0.21/0.51          | ~ (r2_hidden @ X15 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X14 @ X10) @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.21/0.51          | ((k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i]: (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.21/0.51          | ((k1_xboole_0) = (k3_tarski @ k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ($false), inference('sup-', [status(thm)], ['16', '23'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
