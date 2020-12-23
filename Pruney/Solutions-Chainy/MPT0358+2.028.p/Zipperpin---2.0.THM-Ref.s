%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o3KBnRaUyN

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 102 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 ( 779 expanded)
%              Number of equality atoms :   37 (  88 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k1_subset_1 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k1_subset_1 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','11'])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o3KBnRaUyN
% 0.17/0.37  % Computer   : n010.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 10:16:00 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 106 iterations in 0.034s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(t38_subset_1, conjecture,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.23/0.52         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i,B:$i]:
% 0.23/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.23/0.52            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.23/0.52        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.23/0.52        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.23/0.52       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.52  thf('4', plain, (![X12 : $i]: ((k1_subset_1 @ X12) = (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.23/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.23/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.52  thf('10', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.23/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.23/0.52       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.23/0.52       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('13', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['3', '11', '12'])).
% 0.23/0.52  thf('14', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.23/0.52      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.23/0.52  thf(t28_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X7 : $i, X8 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.52  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(d5_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i]:
% 0.23/0.52         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.23/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['16', '19'])).
% 0.23/0.52  thf(t79_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.23/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.23/0.52  thf(d7_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X2 : $i, X3 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('26', plain, (((k1_xboole_0) = (sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['20', '25'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.23/0.52         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf('28', plain, (![X12 : $i]: ((k1_subset_1 @ X12) = (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf('30', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['3', '11'])).
% 0.23/0.52  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.52      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('32', plain, ($false),
% 0.23/0.52      inference('simplify_reflect-', [status(thm)], ['26', '31'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
