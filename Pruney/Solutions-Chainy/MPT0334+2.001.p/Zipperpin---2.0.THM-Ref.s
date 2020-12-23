%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BlqFcrL77y

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:10 EST 2020

% Result     : Theorem 11.41s
% Output     : Refutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 266 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k4_xboole_0 @ X67 @ ( k1_tarski @ X68 ) )
        = X67 )
      | ( r2_hidden @ X68 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X32 @ X34 ) @ X33 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X32 @ X33 ) @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( X49 = X46 )
      | ( X48
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X46: $i,X49: $i] :
      ( ( X49 = X46 )
      | ~ ( r2_hidden @ X49 @ ( k1_tarski @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BlqFcrL77y
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:18:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.41/11.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.41/11.64  % Solved by: fo/fo7.sh
% 11.41/11.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.41/11.64  % done 7631 iterations in 11.183s
% 11.41/11.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.41/11.64  % SZS output start Refutation
% 11.41/11.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 11.41/11.64  thf(sk_A_type, type, sk_A: $i).
% 11.41/11.64  thf(sk_B_type, type, sk_B: $i).
% 11.41/11.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.41/11.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.41/11.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.41/11.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.41/11.64  thf(t65_zfmisc_1, axiom,
% 11.41/11.64    (![A:$i,B:$i]:
% 11.41/11.64     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 11.41/11.64       ( ~( r2_hidden @ B @ A ) ) ))).
% 11.41/11.64  thf('0', plain,
% 11.41/11.64      (![X67 : $i, X68 : $i]:
% 11.41/11.64         (((k4_xboole_0 @ X67 @ (k1_tarski @ X68)) = (X67))
% 11.41/11.64          | (r2_hidden @ X68 @ X67))),
% 11.41/11.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 11.41/11.64  thf(t42_xboole_1, axiom,
% 11.41/11.64    (![A:$i,B:$i,C:$i]:
% 11.41/11.64     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 11.41/11.64       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 11.41/11.64  thf('1', plain,
% 11.41/11.64      (![X32 : $i, X33 : $i, X34 : $i]:
% 11.41/11.64         ((k4_xboole_0 @ (k2_xboole_0 @ X32 @ X34) @ X33)
% 11.41/11.64           = (k2_xboole_0 @ (k4_xboole_0 @ X32 @ X33) @ 
% 11.41/11.64              (k4_xboole_0 @ X34 @ X33)))),
% 11.41/11.64      inference('cnf', [status(esa)], [t42_xboole_1])).
% 11.41/11.64  thf('2', plain,
% 11.41/11.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.41/11.64         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))
% 11.41/11.64            = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0))
% 11.41/11.64          | (r2_hidden @ X1 @ X0))),
% 11.41/11.64      inference('sup+', [status(thm)], ['0', '1'])).
% 11.41/11.64  thf(t147_zfmisc_1, conjecture,
% 11.41/11.64    (![A:$i,B:$i,C:$i]:
% 11.41/11.64     ( ( ( A ) != ( B ) ) =>
% 11.41/11.64       ( ( k4_xboole_0 @
% 11.41/11.64           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 11.41/11.64         ( k2_xboole_0 @
% 11.41/11.64           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 11.41/11.64  thf(zf_stmt_0, negated_conjecture,
% 11.41/11.64    (~( ![A:$i,B:$i,C:$i]:
% 11.41/11.64        ( ( ( A ) != ( B ) ) =>
% 11.41/11.64          ( ( k4_xboole_0 @
% 11.41/11.64              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 11.41/11.64            ( k2_xboole_0 @
% 11.41/11.64              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 11.41/11.64    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 11.41/11.64  thf('3', plain,
% 11.41/11.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 11.41/11.64         (k1_tarski @ sk_B))
% 11.41/11.64         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B)) @ 
% 11.41/11.64             (k1_tarski @ sk_A)))),
% 11.41/11.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.41/11.64  thf(commutativity_k2_xboole_0, axiom,
% 11.41/11.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.41/11.64  thf('4', plain,
% 11.41/11.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.41/11.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.41/11.64  thf('5', plain,
% 11.41/11.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 11.41/11.64         (k1_tarski @ sk_B))
% 11.41/11.64         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 11.41/11.64             (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B))))),
% 11.41/11.64      inference('demod', [status(thm)], ['3', '4'])).
% 11.41/11.64  thf('6', plain,
% 11.41/11.64      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B)) @ 
% 11.41/11.64          (k1_tarski @ sk_A))
% 11.41/11.64          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 11.41/11.64              (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B))))
% 11.41/11.64        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 11.41/11.64      inference('sup-', [status(thm)], ['2', '5'])).
% 11.41/11.64  thf('7', plain,
% 11.41/11.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.41/11.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.41/11.64  thf('8', plain,
% 11.41/11.64      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 11.41/11.64          (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B)))
% 11.41/11.64          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 11.41/11.64              (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_B))))
% 11.41/11.64        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 11.41/11.64      inference('demod', [status(thm)], ['6', '7'])).
% 11.41/11.64  thf('9', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 11.41/11.64      inference('simplify', [status(thm)], ['8'])).
% 11.41/11.64  thf(d1_tarski, axiom,
% 11.41/11.64    (![A:$i,B:$i]:
% 11.41/11.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 11.41/11.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 11.41/11.64  thf('10', plain,
% 11.41/11.64      (![X46 : $i, X48 : $i, X49 : $i]:
% 11.41/11.64         (~ (r2_hidden @ X49 @ X48)
% 11.41/11.64          | ((X49) = (X46))
% 11.41/11.64          | ((X48) != (k1_tarski @ X46)))),
% 11.41/11.64      inference('cnf', [status(esa)], [d1_tarski])).
% 11.41/11.64  thf('11', plain,
% 11.41/11.64      (![X46 : $i, X49 : $i]:
% 11.41/11.64         (((X49) = (X46)) | ~ (r2_hidden @ X49 @ (k1_tarski @ X46)))),
% 11.41/11.64      inference('simplify', [status(thm)], ['10'])).
% 11.41/11.64  thf('12', plain, (((sk_B) = (sk_A))),
% 11.41/11.64      inference('sup-', [status(thm)], ['9', '11'])).
% 11.41/11.64  thf('13', plain, (((sk_A) != (sk_B))),
% 11.41/11.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.41/11.64  thf('14', plain, ($false),
% 11.41/11.64      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 11.41/11.64  
% 11.41/11.64  % SZS output end Refutation
% 11.41/11.64  
% 11.41/11.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
