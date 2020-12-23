%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLF2Y7abpB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:56 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 ( 269 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k10_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D_1 @ X19 @ X17 @ X18 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
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

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLF2Y7abpB
% 0.17/0.37  % Computer   : n023.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 18:57:51 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 55 iterations in 0.036s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.24/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(t172_relat_1, conjecture,
% 0.24/0.53    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.24/0.53  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t60_relat_1, axiom,
% 0.24/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.53  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.53  thf(d3_tarski, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X1 : $i, X3 : $i]:
% 0.24/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.53  thf(t166_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ C ) =>
% 0.24/0.53       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.24/0.53         ( ?[D:$i]:
% 0.24/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.24/0.53             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.24/0.53             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X18 @ (k10_relat_1 @ X19 @ X17))
% 0.24/0.53          | (r2_hidden @ (sk_D_1 @ X19 @ X17 @ X18) @ (k2_relat_1 @ X19))
% 0.24/0.53          | ~ (v1_relat_1 @ X19))),
% 0.24/0.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.24/0.53          | ~ (v1_relat_1 @ X1)
% 0.24/0.53          | (r2_hidden @ 
% 0.24/0.53             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.24/0.53             (k2_relat_1 @ X1)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r2_hidden @ 
% 0.24/0.53           (sk_D_1 @ k1_xboole_0 @ X0 @ 
% 0.24/0.53            (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.24/0.53           k1_xboole_0)
% 0.24/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.53          | (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.24/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.24/0.53  thf(d1_relat_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ A ) <=>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ~( ( r2_hidden @ B @ A ) & 
% 0.24/0.53              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X13 : $i]: ((v1_relat_1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.24/0.53  thf(t2_boole, axiom,
% 0.24/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.53  thf(t4_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.24/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.53  thf('10', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.24/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.53  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.53  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r2_hidden @ 
% 0.24/0.53           (sk_D_1 @ k1_xboole_0 @ X0 @ 
% 0.24/0.53            (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.24/0.53           k1_xboole_0)
% 0.24/0.53          | (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.24/0.53      inference('demod', [status(thm)], ['5', '12'])).
% 0.24/0.53  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0) @ X1)),
% 0.24/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf(t3_xboole_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.24/0.53      inference('demod', [status(thm)], ['0', '17'])).
% 0.24/0.53  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
