%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6F0YrVBwjT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   42 (  60 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 310 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

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
    inference('sup-',[status(thm)],['4','5'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6F0YrVBwjT
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 202 iterations in 0.126s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(d1_xboole_0, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.58  thf(t143_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ C ) =>
% 0.36/0.58       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.36/0.58         ( ?[D:$i]:
% 0.36/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.36/0.58             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.36/0.58             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.36/0.58          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.36/0.58          | ~ (v1_relat_1 @ X12))),
% 0.36/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X1)
% 0.36/0.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.36/0.58             X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf(t113_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i]:
% 0.36/0.58         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.58  thf(t152_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.36/0.58      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.36/0.58  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['2', '6'])).
% 0.36/0.58  thf(l13_xboole_0, axiom,
% 0.36/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.58  thf(t149_relat_1, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( v1_relat_1 @ A ) =>
% 0.36/0.58          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.36/0.58  thf('12', plain, (((k9_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k9_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((X0) != (k1_xboole_0))
% 0.36/0.58          | ~ (v1_xboole_0 @ X0)
% 0.36/0.58          | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1))
% 0.36/0.58          | ~ (v1_xboole_0 @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['10', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X1 : $i]:
% 0.36/0.58         (~ (v1_xboole_0 @ X1)
% 0.36/0.58          | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1))
% 0.36/0.58          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.58  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.58  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X1 : $i]:
% 0.36/0.58         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A @ X1)))),
% 0.36/0.58      inference('simplify_reflect+', [status(thm)], ['15', '18'])).
% 0.36/0.58  thf('20', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['7', '19'])).
% 0.36/0.58  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('23', plain, ($false),
% 0.36/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
