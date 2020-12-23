%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ZJebgwnej

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  356 ( 836 expanded)
%              Number of equality atoms :   59 ( 153 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t10_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) )
        & ~ ( ( ( k7_setfam_1 @ A @ B )
             != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ~ ( ( B != k1_xboole_0 )
              & ( ( k7_setfam_1 @ A @ B )
                = k1_xboole_0 ) )
          & ~ ( ( ( k7_setfam_1 @ A @ B )
               != k1_xboole_0 )
              & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_tops_2])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k7_setfam_1 @ X4 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k7_setfam_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( r1_tarski @ X8 @ ( k7_setfam_1 @ X7 @ X6 ) )
      | ( r1_tarski @ ( k7_setfam_1 @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ZJebgwnej
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 38 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(t10_tops_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.47         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.47            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((sk_B) != (k1_xboole_0))
% 0.21/0.47        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.47        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t46_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (((k7_setfam_1 @ X4 @ X5) != (k1_xboole_0))
% 0.21/0.47          | ((X5) = (k1_xboole_0))
% 0.21/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0))
% 0.21/0.47        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_B) != (sk_B)))
% 0.21/0.47         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.21/0.47             (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0))) | 
% 0.21/0.47       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('14', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t52_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.21/0.47             ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.21/0.47          | ~ (r1_tarski @ X8 @ (k7_setfam_1 @ X7 @ X6))
% 0.21/0.47          | (r1_tarski @ (k7_setfam_1 @ X7 @ X8) @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.48          | (r1_tarski @ (k7_setfam_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.48          | ~ (r1_tarski @ X0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.48        | (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.48         <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (sk_B))))
% 0.21/0.48         <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((k7_setfam_1 @ sk_A @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_B) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.21/0.48             (((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_B) != (sk_B)))
% 0.21/0.48         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.21/0.48             (((sk_B) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.21/0.48       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.48  thf('31', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['1', '11', '12', '30'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
