%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQyN8q8dSr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:58 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  210 ( 210 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQyN8q8dSr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.16/2.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.16/2.41  % Solved by: fo/fo7.sh
% 2.16/2.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.16/2.41  % done 1966 iterations in 1.949s
% 2.16/2.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.16/2.41  % SZS output start Refutation
% 2.16/2.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.16/2.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.16/2.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.16/2.41  thf(sk_B_type, type, sk_B: $i > $i).
% 2.16/2.41  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.16/2.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.16/2.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.16/2.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.16/2.41  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.16/2.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.16/2.41  thf(sk_A_type, type, sk_A: $i).
% 2.16/2.41  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.16/2.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.16/2.41  thf(t8_boole, axiom,
% 2.16/2.41    (![A:$i,B:$i]:
% 2.16/2.41     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.16/2.41  thf('0', plain,
% 2.16/2.41      (![X3 : $i, X4 : $i]:
% 2.16/2.41         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 2.16/2.41      inference('cnf', [status(esa)], [t8_boole])).
% 2.16/2.41  thf(t172_relat_1, conjecture,
% 2.16/2.41    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.16/2.41  thf(zf_stmt_0, negated_conjecture,
% 2.16/2.41    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 2.16/2.41    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 2.16/2.41  thf('1', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 2.16/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.41  thf('2', plain,
% 2.16/2.41      (![X0 : $i]:
% 2.16/2.41         (((X0) != (k1_xboole_0))
% 2.16/2.41          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 2.16/2.41          | ~ (v1_xboole_0 @ X0))),
% 2.16/2.41      inference('sup-', [status(thm)], ['0', '1'])).
% 2.16/2.41  thf('3', plain,
% 2.16/2.41      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.16/2.41        | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 2.16/2.41      inference('simplify', [status(thm)], ['2'])).
% 2.16/2.41  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.16/2.41  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.16/2.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.16/2.41  thf('5', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 2.16/2.41      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 2.16/2.41  thf(t60_relat_1, axiom,
% 2.16/2.41    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.16/2.41     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.16/2.41  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.16/2.41      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.16/2.41  thf(d1_xboole_0, axiom,
% 2.16/2.41    (![A:$i]:
% 2.16/2.41     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.16/2.41  thf('7', plain,
% 2.16/2.41      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.16/2.41      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.16/2.41  thf(t166_relat_1, axiom,
% 2.16/2.41    (![A:$i,B:$i,C:$i]:
% 2.16/2.41     ( ( v1_relat_1 @ C ) =>
% 2.16/2.41       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 2.16/2.41         ( ?[D:$i]:
% 2.16/2.41           ( ( r2_hidden @ D @ B ) & 
% 2.16/2.41             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 2.16/2.41             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 2.16/2.41  thf('8', plain,
% 2.16/2.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.16/2.41         (~ (r2_hidden @ X13 @ (k10_relat_1 @ X14 @ X12))
% 2.16/2.41          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k2_relat_1 @ X14))
% 2.16/2.41          | ~ (v1_relat_1 @ X14))),
% 2.16/2.41      inference('cnf', [status(esa)], [t166_relat_1])).
% 2.16/2.41  thf('9', plain,
% 2.16/2.41      (![X0 : $i, X1 : $i]:
% 2.16/2.41         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 2.16/2.41          | ~ (v1_relat_1 @ X1)
% 2.16/2.41          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 2.16/2.41             (k2_relat_1 @ X1)))),
% 2.16/2.41      inference('sup-', [status(thm)], ['7', '8'])).
% 2.16/2.41  thf('10', plain,
% 2.16/2.41      (![X0 : $i]:
% 2.16/2.41         ((r2_hidden @ 
% 2.16/2.41           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 2.16/2.41           k1_xboole_0)
% 2.16/2.41          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.16/2.41          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 2.16/2.41      inference('sup+', [status(thm)], ['6', '9'])).
% 2.16/2.41  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.16/2.41  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.16/2.41      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.16/2.41  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.16/2.41  thf('12', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.16/2.41      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.41  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.16/2.41      inference('sup+', [status(thm)], ['11', '12'])).
% 2.16/2.41  thf('14', plain,
% 2.16/2.41      (![X0 : $i]:
% 2.16/2.41         ((r2_hidden @ 
% 2.16/2.41           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 2.16/2.41           k1_xboole_0)
% 2.16/2.41          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 2.16/2.41      inference('demod', [status(thm)], ['10', '13'])).
% 2.16/2.41  thf(t113_zfmisc_1, axiom,
% 2.16/2.41    (![A:$i,B:$i]:
% 2.16/2.41     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.16/2.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.16/2.41  thf('15', plain,
% 2.16/2.41      (![X6 : $i, X7 : $i]:
% 2.16/2.41         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 2.16/2.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.16/2.41  thf('16', plain,
% 2.16/2.41      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 2.16/2.41      inference('simplify', [status(thm)], ['15'])).
% 2.16/2.41  thf(t152_zfmisc_1, axiom,
% 2.16/2.41    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.16/2.41  thf('17', plain,
% 2.16/2.41      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.16/2.41      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.16/2.41  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.16/2.41      inference('sup-', [status(thm)], ['16', '17'])).
% 2.16/2.41  thf('19', plain,
% 2.16/2.41      (![X0 : $i]: (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 2.16/2.41      inference('clc', [status(thm)], ['14', '18'])).
% 2.16/2.41  thf('20', plain, ($false), inference('demod', [status(thm)], ['5', '19'])).
% 2.16/2.41  
% 2.16/2.41  % SZS output end Refutation
% 2.16/2.41  
% 2.16/2.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
