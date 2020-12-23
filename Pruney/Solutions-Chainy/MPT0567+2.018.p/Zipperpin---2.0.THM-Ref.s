%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ysa9v7oZKe

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  116 ( 130 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B_1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('5',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ysa9v7oZKe
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 10 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.47  thf(t7_xboole_0, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.47  thf(t166_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.22/0.47         ( ?[D:$i]:
% 0.22/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.47             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.22/0.47             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.22/0.47          | ~ (v1_relat_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (sk_D @ X1 @ X0 @ (sk_B_1 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf(d1_xboole_0, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf(t171_relat_1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ A ) =>
% 0.22/0.47          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.22/0.47  thf('5', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.47  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.47  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.47  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
