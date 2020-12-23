%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfS8BScSt2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :  136 ( 138 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('3',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('5',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','3','4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( v5_ordinal1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf('8',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
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

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['9','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfS8BScSt2
% 0.15/0.37  % Computer   : n003.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:49:27 EST 2020
% 0.22/0.38  % CPUTime    : 
% 0.22/0.38  % Running portfolio for 600 s
% 0.22/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.38  % Number of cores: 8
% 0.22/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 24 iterations in 0.013s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.50  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(t45_ordinal1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.23/0.50       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.23/0.50          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.23/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.23/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.50        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.50  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.50  thf(cc1_funct_1, axiom,
% 0.23/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.23/0.50  thf('2', plain, (![X13 : $i]: ((v1_funct_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.23/0.50  thf('3', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf(l222_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.23/0.50  thf('4', plain, (![X11 : $i]: (v5_relat_1 @ k1_xboole_0 @ X11)),
% 0.23/0.50      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.23/0.50  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.50  thf(cc4_ordinal1, axiom,
% 0.23/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.23/0.50  thf('7', plain, (![X14 : $i]: ((v5_ordinal1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.23/0.50      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.23/0.50  thf('8', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('9', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.23/0.50      inference('demod', [status(thm)], ['5', '8'])).
% 0.23/0.50  thf(d1_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) <=>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ~( ( r2_hidden @ B @ A ) & 
% 0.23/0.50              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X8 : $i]: ((v1_relat_1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.23/0.50  thf(t2_boole, axiom,
% 0.23/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.23/0.50  thf(t4_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.23/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.50  thf('14', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.50  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf('16', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '15'])).
% 0.23/0.50  thf('17', plain, ($false), inference('demod', [status(thm)], ['9', '16'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
