%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WsshCozSaY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  151 ( 223 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) @ X9 )
        = ( k7_relat_1 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t207_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_xboole_0 @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t207_relat_1])).

thf('2',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ( k7_relat_1 @ sk_C_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WsshCozSaY
% 0.13/0.36  % Computer   : n012.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:13:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 12 iterations in 0.007s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.44  thf(t110_relat_1, axiom,
% 0.22/0.44    (![A:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ A ) =>
% 0.22/0.44       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.44  thf('0', plain,
% 0.22/0.44      (![X10 : $i]:
% 0.22/0.44         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.44          | ~ (v1_relat_1 @ X10))),
% 0.22/0.44      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.22/0.44  thf(t100_relat_1, axiom,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ C ) =>
% 0.22/0.44       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.44         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.44  thf('1', plain,
% 0.22/0.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.44         (((k7_relat_1 @ (k7_relat_1 @ X7 @ X8) @ X9)
% 0.22/0.44            = (k7_relat_1 @ X7 @ (k3_xboole_0 @ X8 @ X9)))
% 0.22/0.44          | ~ (v1_relat_1 @ X7))),
% 0.22/0.44      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.44  thf(t207_relat_1, conjecture,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ C ) =>
% 0.22/0.44       ( ( r1_xboole_0 @ A @ B ) =>
% 0.22/0.44         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.44        ( ( v1_relat_1 @ C ) =>
% 0.22/0.44          ( ( r1_xboole_0 @ A @ B ) =>
% 0.22/0.44            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t207_relat_1])).
% 0.22/0.44  thf('2', plain,
% 0.22/0.44      (((k7_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('3', plain,
% 0.22/0.44      ((((k7_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B_1)) != (k1_xboole_0))
% 0.22/0.44        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.44  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(t7_xboole_0, axiom,
% 0.22/0.44    (![A:$i]:
% 0.22/0.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.44          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.44  thf('5', plain,
% 0.22/0.44      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.44      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.44  thf(t4_xboole_0, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.44            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.44  thf('6', plain,
% 0.22/0.44      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.44         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.22/0.44          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.44      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.44  thf('7', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.44  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.44  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('10', plain, (((k7_relat_1 @ sk_C_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.44      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.22/0.44  thf('11', plain,
% 0.22/0.44      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.44      inference('sup-', [status(thm)], ['0', '10'])).
% 0.22/0.44  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.44  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
