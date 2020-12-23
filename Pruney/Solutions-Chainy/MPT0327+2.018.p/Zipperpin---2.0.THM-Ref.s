%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ioPbeLSBJh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:52 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  289 ( 354 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ X30 @ X31 )
        = X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['2','15','16','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ioPbeLSBJh
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:42:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 567 iterations in 0.184s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(t140_zfmisc_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.47/0.64       ( ( k2_xboole_0 @
% 0.47/0.64           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.47/0.64         ( B ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i]:
% 0.47/0.64        ( ( r2_hidden @ A @ B ) =>
% 0.47/0.64          ( ( k2_xboole_0 @
% 0.47/0.64              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.47/0.64            ( B ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.47/0.64         (k1_tarski @ sk_A)) != (sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.47/0.64         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf(t3_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.47/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.64            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i]:
% 0.47/0.64         ((r1_xboole_0 @ X16 @ X17) | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ X17))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i]:
% 0.47/0.64         ((r1_xboole_0 @ X16 @ X17) | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ X16))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.64  thf(d5_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X10 @ X9)
% 0.47/0.64          | ~ (r2_hidden @ X10 @ X8)
% 0.47/0.64          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X10 @ X8)
% 0.47/0.64          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.47/0.64          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '6'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.64          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.47/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.64  thf(t83_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X30 : $i, X31 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X30 @ X31) = (X30)) | ~ (r1_xboole_0 @ X30 @ X31))),
% 0.47/0.64      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.64           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf(t98_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X33 : $i, X34 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ X33 @ X34)
% 0.47/0.64           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.64           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X33 : $i, X34 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ X33 @ X34)
% 0.47/0.64           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.64           = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.64  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(l1_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X45 : $i, X47 : $i]:
% 0.47/0.64         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.47/0.64      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.64  thf('19', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf(t12_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i]:
% 0.47/0.64         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.64  thf('21', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.64  thf('23', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.64  thf('24', plain, (((sk_B) != (sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '15', '16', '23'])).
% 0.47/0.64  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
