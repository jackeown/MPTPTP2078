%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W1STVKugzC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:59 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 ( 283 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k10_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_D_1 @ X21 @ X19 @ X20 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ ( sk_D_1 @ X1 @ X0 @ ( sk_D @ ( k10_relat_1 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W1STVKugzC
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.63/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.84  % Solved by: fo/fo7.sh
% 0.63/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.84  % done 468 iterations in 0.363s
% 0.63/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.84  % SZS output start Refutation
% 0.63/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.63/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.63/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.63/0.84  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.63/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.63/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.63/0.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.63/0.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.63/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.63/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.63/0.84  thf(t172_relat_1, conjecture,
% 0.63/0.84    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.63/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.84    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.63/0.84    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.63/0.84  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf(d5_xboole_0, axiom,
% 0.63/0.84    (![A:$i,B:$i,C:$i]:
% 0.63/0.84     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.63/0.84       ( ![D:$i]:
% 0.63/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.63/0.84           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.63/0.84  thf('1', plain,
% 0.63/0.84      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.63/0.84         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.63/0.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.63/0.84          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.63/0.84      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.84  thf(t2_boole, axiom,
% 0.63/0.84    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.63/0.84  thf('2', plain,
% 0.63/0.84      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.63/0.84      inference('cnf', [status(esa)], [t2_boole])).
% 0.63/0.84  thf(t4_xboole_0, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.63/0.84            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.63/0.84       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.63/0.84            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.63/0.84  thf('3', plain,
% 0.63/0.84      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.63/0.84         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.63/0.84          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.63/0.84      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.63/0.84  thf('4', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i]:
% 0.63/0.84         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.63/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.63/0.84  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.63/0.84  thf('5', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.63/0.84      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.63/0.84  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.63/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.63/0.84  thf('7', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i]:
% 0.63/0.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.63/0.84          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.63/0.84  thf(t4_boole, axiom,
% 0.63/0.84    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.63/0.84  thf('8', plain,
% 0.63/0.84      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.63/0.84      inference('cnf', [status(esa)], [t4_boole])).
% 0.63/0.84  thf('9', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i]:
% 0.63/0.84         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.63/0.84          | ((X1) = (k1_xboole_0)))),
% 0.63/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.84  thf(t166_relat_1, axiom,
% 0.63/0.84    (![A:$i,B:$i,C:$i]:
% 0.63/0.84     ( ( v1_relat_1 @ C ) =>
% 0.63/0.84       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.63/0.84         ( ?[D:$i]:
% 0.63/0.84           ( ( r2_hidden @ D @ B ) & 
% 0.63/0.84             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.63/0.84             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.63/0.84  thf('10', plain,
% 0.63/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.63/0.84         (~ (r2_hidden @ X20 @ (k10_relat_1 @ X21 @ X19))
% 0.63/0.84          | (r2_hidden @ (k4_tarski @ X20 @ (sk_D_1 @ X21 @ X19 @ X20)) @ X21)
% 0.63/0.84          | ~ (v1_relat_1 @ X21))),
% 0.63/0.84      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.63/0.84  thf('11', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.63/0.84          | ~ (v1_relat_1 @ X1)
% 0.63/0.84          | (r2_hidden @ 
% 0.63/0.84             (k4_tarski @ 
% 0.63/0.84              (sk_D @ (k10_relat_1 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.63/0.84              (sk_D_1 @ X1 @ X0 @ 
% 0.63/0.84               (sk_D @ (k10_relat_1 @ X1 @ X0) @ X2 @ k1_xboole_0))) @ 
% 0.63/0.84             X1))),
% 0.63/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.84  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.63/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.63/0.84  thf('13', plain,
% 0.63/0.84      (![X1 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ k1_xboole_0)
% 0.63/0.84          | ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.63/0.84  thf(t113_zfmisc_1, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.63/0.84       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.63/0.84  thf('14', plain,
% 0.63/0.84      (![X14 : $i, X15 : $i]:
% 0.63/0.84         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.63/0.84          | ((X14) != (k1_xboole_0)))),
% 0.63/0.84      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.63/0.84  thf('15', plain,
% 0.63/0.84      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.63/0.84      inference('simplify', [status(thm)], ['14'])).
% 0.63/0.84  thf(fc6_relat_1, axiom,
% 0.63/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.63/0.84  thf('16', plain,
% 0.63/0.84      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.63/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.63/0.84  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.63/0.84      inference('sup+', [status(thm)], ['15', '16'])).
% 0.63/0.84  thf('18', plain,
% 0.63/0.84      (![X1 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.63/0.84      inference('demod', [status(thm)], ['13', '17'])).
% 0.63/0.84  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.63/0.84      inference('demod', [status(thm)], ['0', '18'])).
% 0.63/0.84  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.63/0.84  
% 0.63/0.84  % SZS output end Refutation
% 0.63/0.84  
% 0.69/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
