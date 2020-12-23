%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSpWe2LXZa

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 101 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  281 ( 805 expanded)
%              Number of equality atoms :   36 (  93 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('10',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','20','21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','22'])).

thf('24',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('26',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','20'])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSpWe2LXZa
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:47:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 60 iterations in 0.016s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(t38_subset_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.47       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.47         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.47          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.47            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.47  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d5_subset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i]:
% 0.22/0.47         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.22/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf(t38_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.22/0.47       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.47        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.22/0.47        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.47         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.22/0.47        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.47       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('9', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('split', [status(esa)], ['5'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.47         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.47         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.47             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.47         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.47             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.47  thf(t4_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.47  thf(l32_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.47       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['15', '19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.47       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.47      inference('split', [status(esa)], ['5'])).
% 0.22/0.47  thf('22', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['8', '20', '21'])).
% 0.22/0.47  thf('23', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['6', '22'])).
% 0.22/0.47  thf('24', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '23'])).
% 0.22/0.47  thf('25', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.22/0.47         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.47  thf('28', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['8', '20'])).
% 0.22/0.47  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['27', '28'])).
% 0.22/0.47  thf('30', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
