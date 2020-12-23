%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7b0yQDdOgN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:39 EST 2020

% Result     : Theorem 8.45s
% Output     : Refutation 8.45s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  331 ( 895 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t137_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) )
     => ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) )
       => ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t137_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X8 ) @ ( sk_E @ X8 ) )
        = X8 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_E_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7b0yQDdOgN
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.45/8.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.45/8.65  % Solved by: fo/fo7.sh
% 8.45/8.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.45/8.65  % done 3444 iterations in 8.196s
% 8.45/8.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.45/8.65  % SZS output start Refutation
% 8.45/8.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.45/8.65  thf(sk_E_1_type, type, sk_E_1: $i).
% 8.45/8.65  thf(sk_E_type, type, sk_E: $i > $i).
% 8.45/8.65  thf(sk_C_type, type, sk_C: $i).
% 8.45/8.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.45/8.65  thf(sk_B_type, type, sk_B: $i).
% 8.45/8.65  thf(sk_A_type, type, sk_A: $i).
% 8.45/8.65  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 8.45/8.65  thf(sk_D_2_type, type, sk_D_2: $i).
% 8.45/8.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 8.45/8.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.45/8.65  thf(t137_zfmisc_1, conjecture,
% 8.45/8.65    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.45/8.65     ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 8.45/8.65         ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 8.45/8.65       ( r2_hidden @
% 8.45/8.65         A @ 
% 8.45/8.65         ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ))).
% 8.45/8.65  thf(zf_stmt_0, negated_conjecture,
% 8.45/8.65    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.45/8.65        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 8.45/8.65            ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 8.45/8.65          ( r2_hidden @
% 8.45/8.65            A @ 
% 8.45/8.65            ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )),
% 8.45/8.65    inference('cnf.neg', [status(esa)], [t137_zfmisc_1])).
% 8.45/8.65  thf('0', plain,
% 8.45/8.65      (~ (r2_hidden @ sk_A @ 
% 8.45/8.65          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 8.45/8.65           (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf('1', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf(l139_zfmisc_1, axiom,
% 8.45/8.65    (![A:$i,B:$i,C:$i]:
% 8.45/8.65     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 8.45/8.65          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 8.45/8.65  thf('3', plain,
% 8.45/8.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.45/8.65         (((k4_tarski @ (sk_D_1 @ X8) @ (sk_E @ X8)) = (X8))
% 8.45/8.65          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 8.45/8.65      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 8.45/8.65  thf('4', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 8.45/8.65      inference('sup-', [status(thm)], ['2', '3'])).
% 8.45/8.65  thf(l54_zfmisc_1, axiom,
% 8.45/8.65    (![A:$i,B:$i,C:$i,D:$i]:
% 8.45/8.65     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 8.45/8.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 8.45/8.65  thf('5', plain,
% 8.45/8.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 8.45/8.65         ((r2_hidden @ X11 @ X12)
% 8.45/8.65          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 8.45/8.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 8.45/8.65  thf('6', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i]:
% 8.45/8.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 8.45/8.65          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 8.45/8.65      inference('sup-', [status(thm)], ['4', '5'])).
% 8.45/8.65  thf('7', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_B)),
% 8.45/8.65      inference('sup-', [status(thm)], ['1', '6'])).
% 8.45/8.65  thf('8', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf('9', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i]:
% 8.45/8.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 8.45/8.65          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 8.45/8.65      inference('sup-', [status(thm)], ['4', '5'])).
% 8.45/8.65  thf('10', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_D_2)),
% 8.45/8.65      inference('sup-', [status(thm)], ['8', '9'])).
% 8.45/8.65  thf(d4_xboole_0, axiom,
% 8.45/8.65    (![A:$i,B:$i,C:$i]:
% 8.45/8.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 8.45/8.65       ( ![D:$i]:
% 8.45/8.65         ( ( r2_hidden @ D @ C ) <=>
% 8.45/8.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 8.45/8.65  thf('11', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.45/8.65         (~ (r2_hidden @ X0 @ X1)
% 8.45/8.65          | ~ (r2_hidden @ X0 @ X2)
% 8.45/8.65          | (r2_hidden @ X0 @ X3)
% 8.45/8.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 8.45/8.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 8.45/8.65  thf('12', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.45/8.65         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 8.45/8.65          | ~ (r2_hidden @ X0 @ X2)
% 8.45/8.65          | ~ (r2_hidden @ X0 @ X1))),
% 8.45/8.65      inference('simplify', [status(thm)], ['11'])).
% 8.45/8.65  thf('13', plain,
% 8.45/8.65      (![X0 : $i]:
% 8.45/8.65         (~ (r2_hidden @ (sk_D_1 @ sk_A) @ X0)
% 8.45/8.65          | (r2_hidden @ (sk_D_1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_D_2)))),
% 8.45/8.65      inference('sup-', [status(thm)], ['10', '12'])).
% 8.45/8.65  thf('14', plain,
% 8.45/8.65      ((r2_hidden @ (sk_D_1 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_D_2))),
% 8.45/8.65      inference('sup-', [status(thm)], ['7', '13'])).
% 8.45/8.65  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf('16', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 8.45/8.65      inference('sup-', [status(thm)], ['2', '3'])).
% 8.45/8.65  thf('17', plain,
% 8.45/8.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 8.45/8.65         ((r2_hidden @ X13 @ X14)
% 8.45/8.65          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 8.45/8.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 8.45/8.65  thf('18', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i]:
% 8.45/8.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 8.45/8.65          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 8.45/8.65      inference('sup-', [status(thm)], ['16', '17'])).
% 8.45/8.65  thf('19', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 8.45/8.65      inference('sup-', [status(thm)], ['15', '18'])).
% 8.45/8.65  thf('20', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 8.45/8.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.65  thf('21', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i]:
% 8.45/8.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 8.45/8.65          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 8.45/8.65      inference('sup-', [status(thm)], ['16', '17'])).
% 8.45/8.65  thf('22', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_E_1)),
% 8.45/8.65      inference('sup-', [status(thm)], ['20', '21'])).
% 8.45/8.65  thf('23', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.45/8.65         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 8.45/8.65          | ~ (r2_hidden @ X0 @ X2)
% 8.45/8.65          | ~ (r2_hidden @ X0 @ X1))),
% 8.45/8.65      inference('simplify', [status(thm)], ['11'])).
% 8.45/8.65  thf('24', plain,
% 8.45/8.65      (![X0 : $i]:
% 8.45/8.65         (~ (r2_hidden @ (sk_E @ sk_A) @ X0)
% 8.45/8.65          | (r2_hidden @ (sk_E @ sk_A) @ (k3_xboole_0 @ X0 @ sk_E_1)))),
% 8.45/8.65      inference('sup-', [status(thm)], ['22', '23'])).
% 8.45/8.65  thf('25', plain,
% 8.45/8.65      ((r2_hidden @ (sk_E @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_E_1))),
% 8.45/8.65      inference('sup-', [status(thm)], ['19', '24'])).
% 8.45/8.65  thf('26', plain,
% 8.45/8.65      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 8.45/8.65         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 8.45/8.65          | ~ (r2_hidden @ X13 @ X15)
% 8.45/8.65          | ~ (r2_hidden @ X11 @ X12))),
% 8.45/8.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 8.45/8.65  thf('27', plain,
% 8.45/8.65      (![X0 : $i, X1 : $i]:
% 8.45/8.65         (~ (r2_hidden @ X1 @ X0)
% 8.45/8.65          | (r2_hidden @ (k4_tarski @ X1 @ (sk_E @ sk_A)) @ 
% 8.45/8.65             (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_C @ sk_E_1))))),
% 8.45/8.65      inference('sup-', [status(thm)], ['25', '26'])).
% 8.45/8.65  thf('28', plain,
% 8.45/8.65      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) @ 
% 8.45/8.65        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 8.45/8.65         (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 8.45/8.65      inference('sup-', [status(thm)], ['14', '27'])).
% 8.45/8.65  thf('29', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 8.45/8.65      inference('sup-', [status(thm)], ['2', '3'])).
% 8.45/8.65  thf('30', plain,
% 8.45/8.65      ((r2_hidden @ sk_A @ 
% 8.45/8.65        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 8.45/8.65         (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 8.45/8.65      inference('demod', [status(thm)], ['28', '29'])).
% 8.45/8.65  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 8.45/8.65  
% 8.45/8.65  % SZS output end Refutation
% 8.45/8.65  
% 8.45/8.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
