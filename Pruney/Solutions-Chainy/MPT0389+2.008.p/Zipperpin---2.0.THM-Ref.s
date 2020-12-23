%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4AWVTlXZz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  309 ( 405 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t7_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( r1_tarski @ X12 @ ( k1_setfam_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_C @ X0 @ sk_A ) ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( sk_C @ X12 @ X11 ) )
      | ( r1_tarski @ X12 @ ( k1_setfam_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4AWVTlXZz
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:20:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 25 iterations in 0.026s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.47  thf(t7_setfam_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t7_setfam_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t6_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (((X11) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 0.20/0.47          | (r1_tarski @ X12 @ (k1_setfam_1 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.47  thf(l35_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( r2_hidden @ A @ B ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X6 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0)
% 0.20/0.47              = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(l32_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0)
% 0.20/0.47          | (r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf(t1_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.47       ( r1_tarski @ A @ C ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X4 @ X5)
% 0.20/0.47          | (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '9'])).
% 0.20/0.47  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ sk_A)) @ sk_B)
% 0.20/0.47              = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ X7)
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf(t4_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_setfam_1 @ X9) @ X10) | ~ (r2_hidden @ X10 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.47          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C @ X0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (((X11) = (k1_xboole_0))
% 0.20/0.47          | ~ (r1_tarski @ X12 @ (sk_C @ X12 @ X11))
% 0.20/0.47          | (r1_tarski @ X12 @ (k1_setfam_1 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.47        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((((sk_A) = (k1_xboole_0))
% 0.20/0.47        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
