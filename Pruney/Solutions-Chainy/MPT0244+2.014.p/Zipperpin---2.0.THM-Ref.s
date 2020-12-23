%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wU06gguuwr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 186 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  329 (1446 expanded)
%              Number of equality atoms :   35 ( 214 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('1',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['4','17','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['2','21'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['20','33'])).

thf('35',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['30','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['27','36'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wU06gguuwr
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 44 iterations in 0.019s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(l27_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X22) @ X23) | (r2_hidden @ X22 @ X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.48  thf(t39_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['1'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.48             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.48  thf('13', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['7', '12'])).
% 0.21/0.48  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)) | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['5', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '17', '19'])).
% 0.21/0.48  thf('21', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.21/0.48  thf(t63_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.48          | ~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.48          | (r1_xboole_0 @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]: ((r2_hidden @ sk_B @ X0) | (r1_xboole_0 @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '24'])).
% 0.21/0.48  thf(l1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X19 : $i, X21 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X19) @ X21) | ~ (r2_hidden @ X19 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ sk_A @ X0) | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['2', '21'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.48        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['31'])).
% 0.21/0.48  thf('34', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['20', '33'])).
% 0.21/0.48  thf('35', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.21/0.48  thf('36', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['30', '35'])).
% 0.21/0.48  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '36'])).
% 0.21/0.48  thf(t66_xboole_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.48  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.21/0.48  thf('41', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
