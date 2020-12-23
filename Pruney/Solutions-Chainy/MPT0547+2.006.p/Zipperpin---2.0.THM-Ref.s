%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHEZppa3HQ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  185 ( 199 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_setfam_1 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X23 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X10 )
        = X10 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_setfam_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_setfam_1 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_setfam_1 @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t21_setfam_1,axiom,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_setfam_1 @ X19 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t21_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ( k9_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHEZppa3HQ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 16 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(d2_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.46              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i]:
% 0.20/0.46         ((r1_setfam_1 @ X16 @ X17) | (r2_hidden @ (sk_C @ X17 @ X16) @ X16))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.46  thf(t143_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.46         ( ?[D:$i]:
% 0.20/0.46           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.46             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.46             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X22 @ (k9_relat_1 @ X23 @ X21))
% 0.20/0.46          | (r2_hidden @ (sk_D_1 @ X23 @ X21 @ X22) @ X21)
% 0.20/0.46          | ~ (v1_relat_1 @ X23))),
% 0.20/0.46      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_setfam_1 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X1)
% 0.20/0.46          | (r2_hidden @ 
% 0.20/0.46             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(l22_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.46       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ (k1_tarski @ X11) @ X10) = (X10))
% 0.20/0.46          | ~ (r2_hidden @ X11 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X1)
% 0.20/0.46          | (r1_setfam_1 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.46          | ((k2_xboole_0 @ 
% 0.20/0.46              (k1_tarski @ 
% 0.20/0.46               (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0)))) @ 
% 0.20/0.46              X0) = (X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t49_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X12 : $i, X13 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((X0) != (k1_xboole_0))
% 0.20/0.46          | (r1_setfam_1 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X1)
% 0.20/0.46          | (r1_setfam_1 @ (k9_relat_1 @ X1 @ k1_xboole_0) @ X2))),
% 0.20/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.46  thf(t21_setfam_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X19 : $i]:
% 0.20/0.46         (((X19) = (k1_xboole_0)) | ~ (r1_setfam_1 @ X19 @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t21_setfam_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf(t149_relat_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ A ) =>
% 0.20/0.46          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.20/0.46  thf('10', plain, (((k9_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
