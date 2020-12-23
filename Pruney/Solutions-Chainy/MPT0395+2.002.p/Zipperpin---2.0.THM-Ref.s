%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VbaheE5iHh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 ( 314 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t17_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_setfam_1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t17_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_setfam_1 @ X23 @ X24 )
      | ( r2_hidden @ ( sk_C @ X24 @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_setfam_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( r1_tarski @ ( sk_C @ X24 @ X23 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VbaheE5iHh
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 136 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(t17_setfam_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.20/0.51  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('2', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.51  thf(t43_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.51          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.51          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('6', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X8 : $i, X10 : $i]:
% 0.20/0.51         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.51  thf(d2_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.51              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i]:
% 0.20/0.51         ((r1_setfam_1 @ X23 @ X24) | (r2_hidden @ (sk_C @ X24 @ X23) @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.51  thf(d5_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | (r2_hidden @ X2 @ X5)
% 0.20/0.51          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.20/0.51          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '13'])).
% 0.20/0.51  thf(t3_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('15', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.51          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.51          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.51          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('condensation', [status(thm)], ['18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_setfam_1 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['14', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('22', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         ((r1_setfam_1 @ X23 @ X24)
% 0.20/0.51          | ~ (r2_hidden @ X25 @ X24)
% 0.20/0.51          | ~ (r1_tarski @ (sk_C @ X24 @ X23) @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '24'])).
% 0.20/0.51  thf('26', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.51  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
