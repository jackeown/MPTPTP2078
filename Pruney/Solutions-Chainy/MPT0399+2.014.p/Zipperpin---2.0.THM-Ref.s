%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fQ4RmIL2M0

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 120 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( sk_D @ X35 @ X36 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( r1_setfam_1 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['3','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fQ4RmIL2M0
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 39 iterations in 0.030s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(l13_xboole_0, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf(t21_setfam_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.20/0.50  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('5', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d2_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X35 @ X36) @ X36)
% 0.20/0.50          | ~ (r2_hidden @ X35 @ X37)
% 0.20/0.50          | ~ (r1_setfam_1 @ X37 @ X36))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.50  thf('8', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.50  thf(t55_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X32 @ X33) @ X34)
% 0.20/0.50          | ~ (r2_hidden @ X32 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.50  thf('10', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['7', '10'])).
% 0.20/0.50  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.50  thf('13', plain, ($false), inference('demod', [status(thm)], ['3', '12'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
