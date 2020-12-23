%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vYFGCo4Epf

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:15 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  194 ( 253 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

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

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X14 ) @ ( sk_D @ X13 @ X14 ) ) @ X14 )
      | ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_F @ X7 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( sk_F @ X2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['3','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vYFGCo4Epf
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 58 iterations in 0.058s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.34/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.34/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.54  thf(l13_xboole_0, axiom,
% 0.34/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.54  thf('0', plain,
% 0.34/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.34/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.54  thf(t56_relat_1, conjecture,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ A ) =>
% 0.34/0.54       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.34/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.54    (~( ![A:$i]:
% 0.34/0.54        ( ( v1_relat_1 @ A ) =>
% 0.34/0.54          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.34/0.54            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.34/0.54  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.54  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.34/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.34/0.54  thf(d1_xboole_0, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.34/0.54  thf('4', plain,
% 0.34/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.34/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.34/0.54  thf(d3_relat_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( r1_tarski @ A @ B ) <=>
% 0.34/0.54           ( ![C:$i,D:$i]:
% 0.34/0.54             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.34/0.54               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.34/0.54  thf('5', plain,
% 0.34/0.54      (![X13 : $i, X14 : $i]:
% 0.34/0.54         ((r2_hidden @ (k4_tarski @ (sk_C @ X13 @ X14) @ (sk_D @ X13 @ X14)) @ 
% 0.34/0.54           X14)
% 0.34/0.54          | (r1_tarski @ X14 @ X13)
% 0.34/0.54          | ~ (v1_relat_1 @ X14))),
% 0.34/0.54      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i]: ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('7', plain,
% 0.34/0.54      (![X0 : $i]: (~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.54  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('9', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.34/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.34/0.54  thf(t113_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      (![X9 : $i, X10 : $i]:
% 0.34/0.54         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.34/0.54  thf('11', plain,
% 0.34/0.54      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.34/0.54  thf(t103_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.54     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.34/0.54          ( r2_hidden @ D @ A ) & 
% 0.34/0.54          ( ![E:$i,F:$i]:
% 0.34/0.54            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.34/0.54                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.34/0.54  thf('12', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.54         (~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ X5 @ X6))
% 0.34/0.54          | (r2_hidden @ (sk_F @ X7 @ X6 @ X5) @ X6)
% 0.34/0.54          | ~ (r2_hidden @ X7 @ X4))),
% 0.34/0.54      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.34/0.55  thf('13', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.34/0.55          | ~ (r2_hidden @ X2 @ X1)
% 0.34/0.55          | (r2_hidden @ (sk_F @ X2 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.34/0.55  thf(t152_zfmisc_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.34/0.55  thf('15', plain,
% 0.34/0.55      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.34/0.55      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.34/0.55  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.55  thf('17', plain,
% 0.34/0.55      (![X1 : $i, X2 : $i]:
% 0.34/0.55         (~ (r2_hidden @ X2 @ X1) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.34/0.55      inference('clc', [status(thm)], ['13', '16'])).
% 0.34/0.55  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.34/0.55      inference('sup-', [status(thm)], ['9', '17'])).
% 0.34/0.55  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 0.34/0.55      inference('sup-', [status(thm)], ['4', '18'])).
% 0.34/0.55  thf('20', plain, ($false), inference('demod', [status(thm)], ['3', '19'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
