%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHCpeT6mnE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 528 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( sk_D @ X17 @ X18 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r1_setfam_1 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X12 )
        = X12 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 != X14 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X14 ) )
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) )
     != ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) @ k1_xboole_0 )
 != ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,
    ( ( k1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17','20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mHCpeT6mnE
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 46 iterations in 0.022s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf(t21_setfam_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.22/0.49  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d2_setfam_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.49              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_D @ X17 @ X18) @ X18)
% 0.22/0.49          | ~ (r2_hidden @ X17 @ X19)
% 0.22/0.49          | ~ (r1_setfam_1 @ X19 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.49          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((((sk_A) = (k1_xboole_0))
% 0.22/0.49        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.49  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf(l22_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.49       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (((k2_xboole_0 @ (k1_tarski @ X13) @ X12) = (X12))
% 0.22/0.49          | ~ (r2_hidden @ X13 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((k2_xboole_0 @ (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) @ 
% 0.22/0.49         k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(t1_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('9', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('11', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t20_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49         ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ( A ) != ( B ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (((X15) != (X14))
% 0.22/0.49          | ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X14))
% 0.22/0.49              != (k1_tarski @ X15)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X14 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))
% 0.22/0.49           != (k1_tarski @ X14))),
% 0.22/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.49           != (k1_tarski @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (((k4_xboole_0 @ 
% 0.22/0.49         (k2_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ 
% 0.22/0.49          (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) @ 
% 0.22/0.49         k1_xboole_0) != (k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '14'])).
% 0.22/0.49  thf('16', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.49  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.49           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf(t92_xboole_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('21', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((k1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16', '17', '20', '21', '22'])).
% 0.22/0.49  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
