%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2IwSdsnads

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:39 EST 2020

% Result     : Theorem 3.49s
% Output     : Refutation 3.49s
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

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X6 ) @ ( sk_E @ X6 ) )
        = X6 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

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
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

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
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2IwSdsnads
% 0.12/0.36  % Computer   : n020.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 13:52:07 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 3.49/3.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.49/3.67  % Solved by: fo/fo7.sh
% 3.49/3.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.49/3.67  % done 3045 iterations in 3.191s
% 3.49/3.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.49/3.67  % SZS output start Refutation
% 3.49/3.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.49/3.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.49/3.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 3.49/3.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.49/3.67  thf(sk_E_type, type, sk_E: $i > $i).
% 3.49/3.67  thf(sk_B_type, type, sk_B: $i).
% 3.49/3.67  thf(sk_A_type, type, sk_A: $i).
% 3.49/3.67  thf(sk_C_type, type, sk_C: $i).
% 3.49/3.67  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 3.49/3.67  thf(sk_E_1_type, type, sk_E_1: $i).
% 3.49/3.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.49/3.67  thf(t137_zfmisc_1, conjecture,
% 3.49/3.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.49/3.67     ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.49/3.67         ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 3.49/3.67       ( r2_hidden @
% 3.49/3.67         A @ 
% 3.49/3.67         ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ))).
% 3.49/3.67  thf(zf_stmt_0, negated_conjecture,
% 3.49/3.67    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.49/3.67        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.49/3.67            ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 3.49/3.67          ( r2_hidden @
% 3.49/3.67            A @ 
% 3.49/3.67            ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )),
% 3.49/3.67    inference('cnf.neg', [status(esa)], [t137_zfmisc_1])).
% 3.49/3.67  thf('0', plain,
% 3.49/3.67      (~ (r2_hidden @ sk_A @ 
% 3.49/3.67          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 3.49/3.67           (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf('1', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf(l139_zfmisc_1, axiom,
% 3.49/3.67    (![A:$i,B:$i,C:$i]:
% 3.49/3.67     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.49/3.67          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 3.49/3.67  thf('3', plain,
% 3.49/3.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.49/3.67         (((k4_tarski @ (sk_D_1 @ X6) @ (sk_E @ X6)) = (X6))
% 3.49/3.67          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 3.49/3.67      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 3.49/3.67  thf('4', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 3.49/3.67      inference('sup-', [status(thm)], ['2', '3'])).
% 3.49/3.67  thf(t106_zfmisc_1, axiom,
% 3.49/3.67    (![A:$i,B:$i,C:$i,D:$i]:
% 3.49/3.67     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 3.49/3.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 3.49/3.67  thf('5', plain,
% 3.49/3.67      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.49/3.67         ((r2_hidden @ X9 @ X10)
% 3.49/3.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 3.49/3.67      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 3.49/3.67  thf('6', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i]:
% 3.49/3.67         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 3.49/3.67          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 3.49/3.67      inference('sup-', [status(thm)], ['4', '5'])).
% 3.49/3.67  thf('7', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_B)),
% 3.49/3.67      inference('sup-', [status(thm)], ['1', '6'])).
% 3.49/3.67  thf('8', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf('9', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i]:
% 3.49/3.67         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 3.49/3.67          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 3.49/3.67      inference('sup-', [status(thm)], ['4', '5'])).
% 3.49/3.67  thf('10', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_D_2)),
% 3.49/3.67      inference('sup-', [status(thm)], ['8', '9'])).
% 3.49/3.67  thf(d4_xboole_0, axiom,
% 3.49/3.67    (![A:$i,B:$i,C:$i]:
% 3.49/3.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.49/3.67       ( ![D:$i]:
% 3.49/3.67         ( ( r2_hidden @ D @ C ) <=>
% 3.49/3.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.49/3.67  thf('11', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.49/3.67         (~ (r2_hidden @ X0 @ X1)
% 3.49/3.67          | ~ (r2_hidden @ X0 @ X2)
% 3.49/3.67          | (r2_hidden @ X0 @ X3)
% 3.49/3.67          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 3.49/3.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.49/3.67  thf('12', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.49/3.67         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 3.49/3.67          | ~ (r2_hidden @ X0 @ X2)
% 3.49/3.67          | ~ (r2_hidden @ X0 @ X1))),
% 3.49/3.67      inference('simplify', [status(thm)], ['11'])).
% 3.49/3.67  thf('13', plain,
% 3.49/3.67      (![X0 : $i]:
% 3.49/3.67         (~ (r2_hidden @ (sk_D_1 @ sk_A) @ X0)
% 3.49/3.67          | (r2_hidden @ (sk_D_1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_D_2)))),
% 3.49/3.67      inference('sup-', [status(thm)], ['10', '12'])).
% 3.49/3.67  thf('14', plain,
% 3.49/3.67      ((r2_hidden @ (sk_D_1 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_D_2))),
% 3.49/3.67      inference('sup-', [status(thm)], ['7', '13'])).
% 3.49/3.67  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf('16', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 3.49/3.67      inference('sup-', [status(thm)], ['2', '3'])).
% 3.49/3.67  thf('17', plain,
% 3.49/3.67      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.49/3.67         ((r2_hidden @ X11 @ X12)
% 3.49/3.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 3.49/3.67      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 3.49/3.67  thf('18', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i]:
% 3.49/3.67         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 3.49/3.67          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 3.49/3.67      inference('sup-', [status(thm)], ['16', '17'])).
% 3.49/3.67  thf('19', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 3.49/3.67      inference('sup-', [status(thm)], ['15', '18'])).
% 3.49/3.67  thf('20', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_1))),
% 3.49/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.49/3.67  thf('21', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i]:
% 3.49/3.67         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 3.49/3.67          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 3.49/3.67      inference('sup-', [status(thm)], ['16', '17'])).
% 3.49/3.67  thf('22', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_E_1)),
% 3.49/3.67      inference('sup-', [status(thm)], ['20', '21'])).
% 3.49/3.67  thf('23', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.49/3.67         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 3.49/3.67          | ~ (r2_hidden @ X0 @ X2)
% 3.49/3.67          | ~ (r2_hidden @ X0 @ X1))),
% 3.49/3.67      inference('simplify', [status(thm)], ['11'])).
% 3.49/3.67  thf('24', plain,
% 3.49/3.67      (![X0 : $i]:
% 3.49/3.67         (~ (r2_hidden @ (sk_E @ sk_A) @ X0)
% 3.49/3.67          | (r2_hidden @ (sk_E @ sk_A) @ (k3_xboole_0 @ X0 @ sk_E_1)))),
% 3.49/3.67      inference('sup-', [status(thm)], ['22', '23'])).
% 3.49/3.67  thf('25', plain,
% 3.49/3.67      ((r2_hidden @ (sk_E @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_E_1))),
% 3.49/3.67      inference('sup-', [status(thm)], ['19', '24'])).
% 3.49/3.67  thf('26', plain,
% 3.49/3.67      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 3.49/3.67         ((r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X13))
% 3.49/3.67          | ~ (r2_hidden @ X11 @ X13)
% 3.49/3.67          | ~ (r2_hidden @ X9 @ X10))),
% 3.49/3.67      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 3.49/3.67  thf('27', plain,
% 3.49/3.67      (![X0 : $i, X1 : $i]:
% 3.49/3.67         (~ (r2_hidden @ X1 @ X0)
% 3.49/3.67          | (r2_hidden @ (k4_tarski @ X1 @ (sk_E @ sk_A)) @ 
% 3.49/3.67             (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_C @ sk_E_1))))),
% 3.49/3.67      inference('sup-', [status(thm)], ['25', '26'])).
% 3.49/3.67  thf('28', plain,
% 3.49/3.67      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) @ 
% 3.49/3.67        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 3.49/3.67         (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 3.49/3.67      inference('sup-', [status(thm)], ['14', '27'])).
% 3.49/3.67  thf('29', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 3.49/3.67      inference('sup-', [status(thm)], ['2', '3'])).
% 3.49/3.67  thf('30', plain,
% 3.49/3.67      ((r2_hidden @ sk_A @ 
% 3.49/3.67        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_2) @ 
% 3.49/3.67         (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 3.49/3.67      inference('demod', [status(thm)], ['28', '29'])).
% 3.49/3.67  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 3.49/3.67  
% 3.49/3.67  % SZS output end Refutation
% 3.49/3.67  
% 3.49/3.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
