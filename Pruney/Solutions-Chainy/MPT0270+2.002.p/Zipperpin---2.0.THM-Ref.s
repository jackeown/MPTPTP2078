%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xX3EgF69Am

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  75 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  248 ( 584 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X42 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
      | ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12','19'])).

thf('21',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['14','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xX3EgF69Am
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 181 iterations in 0.081s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(t67_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.54       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.54          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.20/0.54       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(t79_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.20/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('8', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf(t55_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.54         (~ (r1_xboole_0 @ (k2_tarski @ X42 @ X43) @ X44)
% 0.20/0.54          | ~ (r2_hidden @ X42 @ X44))),
% 0.20/0.54      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.54  thf('13', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.20/0.54  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.20/0.54  thf(l27_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X40 : $i, X41 : $i]:
% 0.20/0.54         ((r1_xboole_0 @ (k1_tarski @ X40) @ X41) | (r2_hidden @ X40 @ X41))),
% 0.20/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.54  thf(t83_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ X1 @ X0)
% 0.20/0.54          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.20/0.54       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '12', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['18', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.54        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.54  thf('23', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('24', plain, ($false), inference('demod', [status(thm)], ['14', '23'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
