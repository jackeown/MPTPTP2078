%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lq3Wi8XbQB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  203 ( 322 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t149_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t149_relat_1])).

thf('12',plain,(
    ( k9_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lq3Wi8XbQB
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:18:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 65 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(d1_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf(t143_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.19/0.49         ( ?[D:$i]:
% 0.19/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.19/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.19/0.49          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.19/0.49          | ~ (v1_relat_1 @ X14))),
% 0.19/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X1)
% 0.19/0.49          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.19/0.49             X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf(t3_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('3', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.49  thf(l33_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.49       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X8 @ X9)
% 0.19/0.49          | ((k4_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_tarski @ X8)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.49          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '6'])).
% 0.19/0.49  thf(l13_xboole_0, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf(t149_relat_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ A ) =>
% 0.19/0.49          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.19/0.49  thf('12', plain, (((k9_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k9_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X0) != (k1_xboole_0))
% 0.19/0.49          | ~ (v1_xboole_0 @ X0)
% 0.19/0.49          | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1))
% 0.19/0.49          | ~ (v1_xboole_0 @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X1 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X1)
% 0.19/0.49          | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1))
% 0.19/0.49          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.49  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X1 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1)))),
% 0.19/0.49      inference('simplify_reflect+', [status(thm)], ['15', '18'])).
% 0.19/0.49  thf('20', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '19'])).
% 0.19/0.49  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('23', plain, ($false),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
