%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qu4IDByirR

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  73 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   20
%              Number of atoms          :  330 ( 702 expanded)
%              Number of equality atoms :   78 ( 147 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t66_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
         != k1_xboole_0 )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
           => ( ( C
               != ( k1_mcart_1 @ C ) )
              & ( C
               != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_mcart_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4
       != ( k1_mcart_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k2_zfmisc_1 @ X3 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k1_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4
       != ( k2_mcart_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k2_zfmisc_1 @ X3 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k2_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','21'])).

thf('23',plain,(
    sk_C
 != ( k2_mcart_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('35',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qu4IDByirR
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 18 iterations in 0.012s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.43  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.43  thf(t66_mcart_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.43       ( ![C:$i]:
% 0.20/0.43         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.43           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.43          ( ![C:$i]:
% 0.20/0.43            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.43              ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.43                ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t66_mcart_1])).
% 0.20/0.43  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('1', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t26_mcart_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.43          ( ~( ![C:$i]:
% 0.20/0.43               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.43                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.43                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.43         (((X3) = (k1_xboole_0))
% 0.20/0.43          | ((X4) != (k1_mcart_1 @ X4))
% 0.20/0.43          | ~ (m1_subset_1 @ X4 @ (k2_zfmisc_1 @ X3 @ X5))
% 0.20/0.43          | ((X5) = (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      ((((sk_B) = (k1_xboole_0))
% 0.20/0.43        | ((sk_C) != (k1_mcart_1 @ sk_C))
% 0.20/0.43        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('split', [status(esa)], ['4'])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('split', [status(esa)], ['4'])).
% 0.20/0.43  thf('7', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.43         (((X3) = (k1_xboole_0))
% 0.20/0.43          | ((X4) != (k2_mcart_1 @ X4))
% 0.20/0.43          | ~ (m1_subset_1 @ X4 @ (k2_zfmisc_1 @ X3 @ X5))
% 0.20/0.43          | ((X5) = (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      ((((sk_B) = (k1_xboole_0))
% 0.20/0.43        | ((sk_C) != (k2_mcart_1 @ sk_C))
% 0.20/0.43        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      (((((sk_C) != (sk_C))
% 0.20/0.43         | ((sk_A) = (k1_xboole_0))
% 0.20/0.43         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.43         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.43  thf('12', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.43         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.43  thf(t113_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X1 : $i, X2 : $i]:
% 0.20/0.43         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.43  thf('15', plain,
% 0.20/0.43      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.43         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('demod', [status(thm)], ['13', '15'])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.43  thf('18', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('19', plain,
% 0.20/0.43      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.20/0.43         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.43  thf('20', plain,
% 0.20/0.43      (![X1 : $i, X2 : $i]:
% 0.20/0.43         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.43  thf('21', plain,
% 0.20/0.43      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.43  thf('22', plain,
% 0.20/0.43      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.43      inference('demod', [status(thm)], ['19', '21'])).
% 0.20/0.43  thf('23', plain, (~ (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.43      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.43  thf('24', plain,
% 0.20/0.43      ((((sk_C) = (k1_mcart_1 @ sk_C))) | (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.43      inference('split', [status(esa)], ['4'])).
% 0.20/0.43  thf('25', plain, ((((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.43      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.43  thf('26', plain, (((sk_C) = (k1_mcart_1 @ sk_C))),
% 0.20/0.43      inference('simpl_trail', [status(thm)], ['5', '25'])).
% 0.20/0.43  thf('27', plain,
% 0.20/0.43      ((((sk_B) = (k1_xboole_0))
% 0.20/0.43        | ((sk_C) != (sk_C))
% 0.20/0.43        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('demod', [status(thm)], ['3', '26'])).
% 0.20/0.43  thf('28', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.43      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.43  thf('29', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('30', plain,
% 0.20/0.43      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.43        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.43  thf('31', plain,
% 0.20/0.43      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.43  thf('32', plain,
% 0.20/0.43      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.43      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.43  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.43  thf('34', plain,
% 0.20/0.43      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.43  thf('35', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['0', '33', '34'])).
% 0.20/0.43  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
