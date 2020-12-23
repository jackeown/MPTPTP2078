%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v0EChv7JIb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:50 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  365 ( 543 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X29: $i,X32: $i] :
      ( r2_hidden @ X29 @ ( k2_tarski @ X32 @ X29 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X31 )
      | ( X33 = X32 )
      | ( X33 = X29 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('8',plain,(
    ! [X29: $i,X32: $i,X33: $i] :
      ( ( X33 = X29 )
      | ( X33 = X32 )
      | ~ ( r2_hidden @ X33 @ ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('25',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22','23','24'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X22 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('30',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v0EChv7JIb
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 330 iterations in 0.254s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.75  thf(t45_zfmisc_1, conjecture,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.53/0.75       ( r2_hidden @ A @ B ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i,B:$i]:
% 0.53/0.75        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.53/0.75          ( r2_hidden @ A @ B ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.53/0.75  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t69_enumset1, axiom,
% 0.53/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.75  thf('1', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.53/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.75  thf(d2_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.53/0.75       ( ![D:$i]:
% 0.53/0.75         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.53/0.75         (((X30) != (X29))
% 0.53/0.75          | (r2_hidden @ X30 @ X31)
% 0.53/0.75          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d2_tarski])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X29 : $i, X32 : $i]: (r2_hidden @ X29 @ (k2_tarski @ X32 @ X29))),
% 0.53/0.75      inference('simplify', [status(thm)], ['2'])).
% 0.53/0.75  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['1', '3'])).
% 0.53/0.75  thf(t3_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.75  thf('6', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.53/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X33 @ X31)
% 0.53/0.75          | ((X33) = (X32))
% 0.53/0.75          | ((X33) = (X29))
% 0.53/0.75          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d2_tarski])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X29 : $i, X32 : $i, X33 : $i]:
% 0.53/0.75         (((X33) = (X29))
% 0.53/0.75          | ((X33) = (X32))
% 0.53/0.75          | ~ (r2_hidden @ X33 @ (k2_tarski @ X32 @ X29)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['6', '8'])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.53/0.75          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '10'])).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ X1)
% 0.53/0.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.53/0.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.53/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X14 : $i, X16 : $i]:
% 0.53/0.75         (((X14) = (X16))
% 0.53/0.75          | ~ (r1_tarski @ X16 @ X14)
% 0.53/0.75          | ~ (r1_tarski @ X14 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.53/0.75        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.75  thf(commutativity_k2_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      (![X27 : $i, X28 : $i]:
% 0.53/0.75         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.53/0.75  thf(l51_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X45 : $i, X46 : $i]:
% 0.53/0.75         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.53/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (![X45 : $i, X46 : $i]:
% 0.53/0.75         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.53/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['20', '21'])).
% 0.53/0.75  thf(t7_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.53/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['20', '21'])).
% 0.53/0.75  thf('25', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['17', '22', '23', '24'])).
% 0.53/0.75  thf(t70_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.53/0.75       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X19 @ X22)
% 0.53/0.75          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ sk_B)
% 0.53/0.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['14', '27'])).
% 0.53/0.75  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['1', '3'])).
% 0.53/0.75  thf('30', plain,
% 0.53/0.75      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X12 @ X10)
% 0.53/0.75          | ~ (r2_hidden @ X12 @ X13)
% 0.53/0.75          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['28', '31'])).
% 0.53/0.75  thf('33', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.53/0.75      inference('sup-', [status(thm)], ['4', '32'])).
% 0.53/0.75  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
