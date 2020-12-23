%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vbeyg63JX2

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  33 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 218 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('0',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k9_relat_1 @ X5 @ X6 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('11',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vbeyg63JX2
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.33  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 11 iterations in 0.007s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(t152_relat_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.44            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.44            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( v1_relat_1 @ B ) =>
% 0.19/0.44          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.44               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.44               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.19/0.44  thf('0', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(t151_relat_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.44         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      (![X5 : $i, X6 : $i]:
% 0.19/0.44         (((k9_relat_1 @ X5 @ X6) != (k1_xboole_0))
% 0.19/0.44          | (r1_xboole_0 @ (k1_relat_1 @ X5) @ X6)
% 0.19/0.44          | ~ (v1_relat_1 @ X5))),
% 0.19/0.44      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.44        | ~ (v1_relat_1 @ sk_B)
% 0.19/0.44        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.44  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.44        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.44  thf('5', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.19/0.44      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.44  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(t63_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.44       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.44         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.44          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.19/0.44          | (r1_xboole_0 @ X0 @ X2))),
% 0.19/0.44      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ sk_A @ X0)
% 0.19/0.44          | ~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.44  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.19/0.44      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.44  thf(t66_xboole_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.44       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X4))),
% 0.19/0.44      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.44  thf('11', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.44  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('13', plain, ($false),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
