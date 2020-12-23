%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7llyxlGUc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 168 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :   20
%              Number of atoms          :  359 (1468 expanded)
%              Number of equality atoms :   54 ( 223 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('3',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t66_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( X10
       != ( k1_mcart_1 @ X10 ) )
      | ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf('5',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
     != ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('9',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( X10
       != ( k2_mcart_1 @ X10 ) )
      | ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf('11',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
     != ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X5 ) @ X4 )
        = X4 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ k1_xboole_0 )
          = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('25',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['7','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['5','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','28'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X5 ) @ X4 )
        = X4 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7llyxlGUc
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 40 iterations in 0.011s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t67_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.47       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.47          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t67_mcart_1])).
% 0.20/0.47  thf('0', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t1_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.47  thf('3', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t66_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.47           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.20/0.47          | ((X10) != (k1_mcart_1 @ X10))
% 0.20/0.47          | ((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t66_mcart_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) != (k1_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('9', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.20/0.47          | ((X10) != (k2_mcart_1 @ X10))
% 0.20/0.47          | ((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t66_mcart_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) != (k2_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((((sk_A) != (sk_A)) | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))))
% 0.20/0.47         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf('14', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(t48_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.47       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ X4)
% 0.20/0.47          | ((k2_xboole_0 @ (k2_tarski @ X3 @ X5) @ X4) = (X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.47             = (k1_xboole_0))
% 0.20/0.47           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.20/0.47          = (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('20', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.47         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf(t49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.47  thf('23', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('25', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((sk_A) = (k1_mcart_1 @ sk_A))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['7', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '26'])).
% 0.20/0.47  thf('28', plain, (((k2_zfmisc_1 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.47  thf('30', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ X4)
% 0.20/0.47          | ((k2_xboole_0 @ (k2_tarski @ X3 @ X5) @ X4) = (X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.47            = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.47  thf('34', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.47  thf('37', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
