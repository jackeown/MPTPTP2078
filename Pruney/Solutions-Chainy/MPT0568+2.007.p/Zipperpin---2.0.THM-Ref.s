%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgY61Efnqz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:48 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  206 ( 208 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('1',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['3','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['5','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgY61Efnqz
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.96  % Solved by: fo/fo7.sh
% 0.74/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.96  % done 1072 iterations in 0.508s
% 0.74/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.96  % SZS output start Refutation
% 0.74/0.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.96  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.74/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.96  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.96  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.74/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.96  thf(t8_boole, axiom,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.74/0.96  thf('0', plain,
% 0.74/0.96      (![X3 : $i, X4 : $i]:
% 0.74/0.96         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.74/0.96      inference('cnf', [status(esa)], [t8_boole])).
% 0.74/0.96  thf(t172_relat_1, conjecture,
% 0.74/0.96    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.74/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.96    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.74/0.96    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.74/0.96  thf('1', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('2', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (((X0) != (k1_xboole_0))
% 0.74/0.96          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 0.74/0.96          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['0', '1'])).
% 0.74/0.96  thf('3', plain,
% 0.74/0.96      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.74/0.96        | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.74/0.96      inference('simplify', [status(thm)], ['2'])).
% 0.74/0.96  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.74/0.96  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.97  thf('5', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.74/0.97      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 0.74/0.97  thf(t60_relat_1, axiom,
% 0.74/0.97    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.74/0.97     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.74/0.97  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.74/0.97  thf(d1_xboole_0, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.97  thf('7', plain,
% 0.74/0.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.97  thf(t166_relat_1, axiom,
% 0.74/0.97    (![A:$i,B:$i,C:$i]:
% 0.74/0.97     ( ( v1_relat_1 @ C ) =>
% 0.74/0.97       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.74/0.97         ( ?[D:$i]:
% 0.74/0.97           ( ( r2_hidden @ D @ B ) & 
% 0.74/0.97             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.74/0.97             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.74/0.97  thf('8', plain,
% 0.74/0.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.74/0.97         (~ (r2_hidden @ X13 @ (k10_relat_1 @ X14 @ X12))
% 0.74/0.97          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k2_relat_1 @ X14))
% 0.74/0.97          | ~ (v1_relat_1 @ X14))),
% 0.74/0.97      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.74/0.97  thf('9', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 0.74/0.97          | ~ (v1_relat_1 @ X1)
% 0.74/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.74/0.97             (k2_relat_1 @ X1)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.97  thf('10', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((r2_hidden @ 
% 0.74/0.97           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.74/0.97           k1_xboole_0)
% 0.74/0.97          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.74/0.97          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.74/0.97      inference('sup+', [status(thm)], ['6', '9'])).
% 0.74/0.97  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.97  thf(cc1_relat_1, axiom,
% 0.74/0.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.74/0.97  thf('12', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.74/0.97      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.74/0.97  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.74/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.97  thf('14', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((r2_hidden @ 
% 0.74/0.97           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.74/0.97           k1_xboole_0)
% 0.74/0.97          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.74/0.97      inference('demod', [status(thm)], ['10', '13'])).
% 0.74/0.97  thf(t113_zfmisc_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.74/0.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.74/0.97  thf('15', plain,
% 0.74/0.97      (![X6 : $i, X7 : $i]:
% 0.74/0.97         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.74/0.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.97  thf('16', plain,
% 0.74/0.97      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.97      inference('simplify', [status(thm)], ['15'])).
% 0.74/0.97  thf(t152_zfmisc_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.74/0.97  thf('17', plain,
% 0.74/0.97      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.74/0.97      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.74/0.97  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.97      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.97  thf('19', plain,
% 0.74/0.97      (![X0 : $i]: (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.74/0.97      inference('clc', [status(thm)], ['14', '18'])).
% 0.74/0.97  thf('20', plain, ($false), inference('demod', [status(thm)], ['5', '19'])).
% 0.74/0.97  
% 0.74/0.97  % SZS output end Refutation
% 0.74/0.97  
% 0.80/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
