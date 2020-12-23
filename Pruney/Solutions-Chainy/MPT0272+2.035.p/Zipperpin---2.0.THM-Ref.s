%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7BRM5enfHI

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 192 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X31 @ X33 ) @ X34 )
        = ( k1_tarski @ X31 ) )
      | ( X31 != X33 )
      | ( r2_hidden @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X33 @ X33 ) @ X34 )
        = ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['5'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ X30 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ X30 )
        = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7BRM5enfHI
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 31 iterations in 0.011s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t69_enumset1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.46  thf('0', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf(l38_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.46       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.46         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ (k2_tarski @ X31 @ X33) @ X34) = (k1_tarski @ X31))
% 0.21/0.46          | ((X31) != (X33))
% 0.21/0.46          | (r2_hidden @ X31 @ X34))),
% 0.21/0.46      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X33 : $i, X34 : $i]:
% 0.21/0.46         ((r2_hidden @ X33 @ X34)
% 0.21/0.46          | ((k4_xboole_0 @ (k2_tarski @ X33 @ X33) @ X34) = (k1_tarski @ X33)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.21/0.46          | (r2_hidden @ X0 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.46  thf(t69_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.21/0.46       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.21/0.46          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.46  thf(l35_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.46       ( r2_hidden @ A @ B ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X28 : $i, X30 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ (k1_tarski @ X28) @ X30) = (k1_xboole_0))
% 0.21/0.46          | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.46      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.21/0.46  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.46  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X28 : $i, X30 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ (k1_tarski @ X28) @ X30) = (o_0_0_xboole_0))
% 0.21/0.46          | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('12', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (o_0_0_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.46  thf('14', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
