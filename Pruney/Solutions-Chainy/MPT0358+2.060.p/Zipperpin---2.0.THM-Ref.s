%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3sJlpftMFa

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 146 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  363 (1153 expanded)
%              Number of equality atoms :   36 ( 125 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k1_subset_1 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('6',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k1_subset_1 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','12'])).

thf('26',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k1_tarski @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','25'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3sJlpftMFa
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:34 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 41 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(t7_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(t38_subset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.47         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.47            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.21/0.47        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.21/0.47         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.21/0.47        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('5', plain, (![X16 : $i]: ((k1_subset_1 @ X16) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.21/0.47         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.21/0.47             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('11', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.21/0.47       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.21/0.47       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['1'])).
% 0.21/0.47  thf('14', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['4', '12', '13'])).
% 0.21/0.47  thf('15', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['2', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(l1_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X13 : $i, X15 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_tarski @ X13) @ X15) | ~ (r2_hidden @ X13 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf(t1_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.47       ( r1_tarski @ A @ C ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X9 @ X10)
% 0.21/0.47          | ~ (r1_tarski @ X10 @ X11)
% 0.21/0.47          | (r1_tarski @ X9 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0))
% 0.21/0.47          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.21/0.47          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.21/0.47         (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.47        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.21/0.47         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('23', plain, (![X16 : $i]: ((k1_subset_1 @ X16) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['4', '12'])).
% 0.21/0.47  thf('26', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.21/0.47        (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['21', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         ((r2_hidden @ X13 @ X14) | ~ (r1_tarski @ (k1_tarski @ X13) @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.21/0.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.47  thf(d5_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.47          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.47          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.47          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.47  thf('36', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.47  thf('37', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '36'])).
% 0.21/0.47  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('39', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
