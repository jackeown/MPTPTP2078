%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNs9vfXhiV

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  60 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 451 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNs9vfXhiV
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 27 iterations in 0.014s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(t68_zfmisc_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48       ( r2_hidden @ A @ B ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48          ( r2_hidden @ A @ B ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.48       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B)
% 0.22/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.22/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf(l32_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.48         | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))
% 0.22/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.48  thf(t69_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf(t38_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         ((r2_hidden @ X8 @ X9) | ~ (r1_tarski @ (k2_tarski @ X8 @ X10) @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B))
% 0.22/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.48       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.22/0.48         ((r1_tarski @ (k2_tarski @ X8 @ X10) @ X11)
% 0.22/0.48          | ~ (r2_hidden @ X10 @ X11)
% 0.22/0.48          | ~ (r2_hidden @ X8 @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((![X0 : $i]:
% 0.22/0.48          (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.48           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B)))
% 0.22/0.48         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B))
% 0.22/0.48         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.48  thf('19', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.48         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i, X2 : $i]:
% 0.22/0.48         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.22/0.48         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.48             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.48  thf('26', plain, ($false),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['1', '12', '13', '25'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
