%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ps5xYNzxtA

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 ( 833 expanded)
%              Number of equality atoms :   68 ( 150 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( ( k7_setfam_1 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ( r2_hidden @ ( k3_subset_1 @ X7 @ ( sk_D @ X6 @ X8 @ X7 ) ) @ X8 )
      | ( X6
        = ( k7_setfam_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ps5xYNzxtA
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 96 iterations in 0.091s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.22/0.55  thf(t10_tops_2, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.55         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.55            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((((sk_B) != (k1_xboole_0))
% 0.22/0.55        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.22/0.55       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.55         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t46_setfam_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i]:
% 0.22/0.55         (((k7_setfam_1 @ X10 @ X11) != (k1_xboole_0))
% 0.22/0.55          | ((X11) = (k1_xboole_0))
% 0.22/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.22/0.55         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0)))
% 0.22/0.55         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((((sk_B) != (sk_B)))
% 0.22/0.55         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.22/0.55             (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))) | 
% 0.22/0.55       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))) | 
% 0.22/0.55       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(d8_setfam_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.22/0.55             ( ![D:$i]:
% 0.22/0.55               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55                 ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.55                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.22/0.55          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.22/0.55          | (r2_hidden @ (k3_subset_1 @ X7 @ (sk_D @ X6 @ X8 @ X7)) @ X8)
% 0.22/0.55          | ((X6) = (k7_setfam_1 @ X7 @ X8))
% 0.22/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.22/0.55      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.22/0.55          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.22/0.55          | (r2_hidden @ (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.22/0.55             X1)
% 0.22/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.22/0.55             k1_xboole_0)
% 0.22/0.55          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.55  thf(t113_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i]:
% 0.22/0.55         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.55  thf(t152_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.55  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.22/0.55             k1_xboole_0))),
% 0.22/0.55      inference('clc', [status(thm)], ['18', '22'])).
% 0.22/0.55  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      ((![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.22/0.55         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('sup+', [status(thm)], ['13', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((![X0 : $i]: ((sk_B) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.22/0.55         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.22/0.55         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((((sk_B) != (k1_xboole_0)))
% 0.22/0.55         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.55             (((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      ((((sk_B) != (sk_B)))
% 0.22/0.55         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.55             (((sk_B) = (k1_xboole_0))))),
% 0.22/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.22/0.55       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.55  thf('34', plain, ($false),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['1', '11', '12', '33'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
