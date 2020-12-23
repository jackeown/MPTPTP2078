%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PalKoA3m5g

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:49 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 ( 237 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
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

thf('9',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ( X9 = X10 ) ) ),
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

thf('18',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PalKoA3m5g
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:40:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.71/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.91  % Solved by: fo/fo7.sh
% 0.71/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.91  % done 737 iterations in 0.474s
% 0.71/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.91  % SZS output start Refutation
% 0.71/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.71/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.91  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.71/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.71/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.91  thf(d1_xboole_0, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.91  thf('0', plain,
% 0.71/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.71/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.91  thf(t166_relat_1, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ( v1_relat_1 @ C ) =>
% 0.71/0.91       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.71/0.91         ( ?[D:$i]:
% 0.71/0.91           ( ( r2_hidden @ D @ B ) & 
% 0.71/0.91             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.71/0.91             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.71/0.91  thf('1', plain,
% 0.71/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.71/0.91          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k2_relat_1 @ X15))
% 0.71/0.91          | ~ (v1_relat_1 @ X15))),
% 0.71/0.91      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.71/0.91  thf('2', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 0.71/0.91          | ~ (v1_relat_1 @ X1)
% 0.71/0.91          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.71/0.91             (k2_relat_1 @ X1)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['0', '1'])).
% 0.71/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.91  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.91  thf(t8_boole, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.71/0.91  thf('4', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X9) | ~ (v1_xboole_0 @ X10) | ((X9) = (X10)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t8_boole])).
% 0.71/0.91  thf('5', plain,
% 0.71/0.91      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.71/0.91  thf(t60_relat_1, axiom,
% 0.71/0.91    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.71/0.91     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.91  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.91  thf('7', plain,
% 0.71/0.91      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup+', [status(thm)], ['5', '6'])).
% 0.71/0.91  thf(t2_boole, axiom,
% 0.71/0.91    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.91  thf('8', plain,
% 0.71/0.91      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.91      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.91  thf(t4_xboole_0, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.71/0.91            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.71/0.91  thf('9', plain,
% 0.71/0.91      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.71/0.91          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.71/0.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.71/0.91  thf('10', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['8', '9'])).
% 0.71/0.91  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.71/0.91  thf('11', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.71/0.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.71/0.91  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.71/0.91      inference('demod', [status(thm)], ['10', '11'])).
% 0.71/0.91  thf('13', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['7', '12'])).
% 0.71/0.91  thf('14', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (v1_relat_1 @ X0)
% 0.71/0.91          | (v1_xboole_0 @ (k10_relat_1 @ X0 @ X1))
% 0.71/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['2', '13'])).
% 0.71/0.91  thf(cc1_relat_1, axiom,
% 0.71/0.91    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.71/0.91  thf('15', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.71/0.91      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.71/0.91  thf('16', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k10_relat_1 @ X0 @ X1)))),
% 0.71/0.91      inference('clc', [status(thm)], ['14', '15'])).
% 0.71/0.91  thf('17', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X9) | ~ (v1_xboole_0 @ X10) | ((X9) = (X10)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t8_boole])).
% 0.71/0.91  thf(t172_relat_1, conjecture,
% 0.71/0.91    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.71/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.91    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.71/0.91    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.71/0.91  thf('18', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('19', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (((X0) != (k1_xboole_0))
% 0.71/0.91          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 0.71/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['17', '18'])).
% 0.71/0.91  thf('20', plain,
% 0.71/0.91      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.71/0.91        | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.71/0.91      inference('simplify', [status(thm)], ['19'])).
% 0.71/0.91  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.91  thf('22', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('simplify_reflect+', [status(thm)], ['20', '21'])).
% 0.71/0.91  thf('23', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.91      inference('sup-', [status(thm)], ['16', '22'])).
% 0.71/0.91  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.91  thf('25', plain, ($false), inference('demod', [status(thm)], ['23', '24'])).
% 0.71/0.91  
% 0.71/0.91  % SZS output end Refutation
% 0.71/0.91  
% 0.71/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
