%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3U3YqX63NL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:39 EST 2020

% Result     : Theorem 54.52s
% Output     : Refutation 54.52s
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

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_4 ) @ ( k3_xboole_0 @ sk_C @ sk_E_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_4 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k4_tarski @ ( sk_D_3 @ X28 ) @ ( sk_E_2 @ X28 ) )
        = X28 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D_3 @ sk_A ) @ ( sk_E_2 @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_D_3 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_4 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_3 @ sk_A ) @ sk_D_4 ),
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
      ( ~ ( r2_hidden @ ( sk_D_3 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_4 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_3 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D_3 @ sk_A ) @ ( sk_E_2 @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_E_2 @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_4 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,(
    r2_hidden @ ( sk_E_2 @ sk_A ) @ sk_E_3 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_2 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_E_2 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_E_3 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E_2 @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_E_3 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X39 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E_2 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_E_3 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_A ) @ ( sk_E_2 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_4 ) @ ( k3_xboole_0 @ sk_C @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ( k4_tarski @ ( sk_D_3 @ sk_A ) @ ( sk_E_2 @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B @ sk_D_4 ) @ ( k3_xboole_0 @ sk_C @ sk_E_3 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3U3YqX63NL
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 54.52/54.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.52/54.72  % Solved by: fo/fo7.sh
% 54.52/54.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.52/54.72  % done 25613 iterations in 54.253s
% 54.52/54.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.52/54.72  % SZS output start Refutation
% 54.52/54.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.52/54.72  thf(sk_D_3_type, type, sk_D_3: $i > $i).
% 54.52/54.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 54.52/54.72  thf(sk_D_4_type, type, sk_D_4: $i).
% 54.52/54.72  thf(sk_C_type, type, sk_C: $i).
% 54.52/54.72  thf(sk_E_2_type, type, sk_E_2: $i > $i).
% 54.52/54.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 54.52/54.72  thf(sk_E_3_type, type, sk_E_3: $i).
% 54.52/54.72  thf(sk_A_type, type, sk_A: $i).
% 54.52/54.72  thf(sk_B_type, type, sk_B: $i).
% 54.52/54.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 54.52/54.72  thf(t137_zfmisc_1, conjecture,
% 54.52/54.72    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 54.52/54.72     ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 54.52/54.72         ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 54.52/54.72       ( r2_hidden @
% 54.52/54.72         A @ 
% 54.52/54.72         ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ))).
% 54.52/54.72  thf(zf_stmt_0, negated_conjecture,
% 54.52/54.72    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 54.52/54.72        ( ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 54.52/54.72            ( r2_hidden @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) =>
% 54.52/54.72          ( r2_hidden @
% 54.52/54.72            A @ 
% 54.52/54.72            ( k2_zfmisc_1 @ ( k3_xboole_0 @ B @ D ) @ ( k3_xboole_0 @ C @ E ) ) ) ) )),
% 54.52/54.72    inference('cnf.neg', [status(esa)], [t137_zfmisc_1])).
% 54.52/54.72  thf('0', plain,
% 54.52/54.72      (~ (r2_hidden @ sk_A @ 
% 54.52/54.72          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_4) @ 
% 54.52/54.72           (k3_xboole_0 @ sk_C @ sk_E_3)))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf('1', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_4 @ sk_E_3))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf(l139_zfmisc_1, axiom,
% 54.52/54.72    (![A:$i,B:$i,C:$i]:
% 54.52/54.72     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 54.52/54.72          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 54.52/54.72  thf('3', plain,
% 54.52/54.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 54.52/54.72         (((k4_tarski @ (sk_D_3 @ X28) @ (sk_E_2 @ X28)) = (X28))
% 54.52/54.72          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 54.52/54.72      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 54.52/54.72  thf('4', plain, (((k4_tarski @ (sk_D_3 @ sk_A) @ (sk_E_2 @ sk_A)) = (sk_A))),
% 54.52/54.72      inference('sup-', [status(thm)], ['2', '3'])).
% 54.52/54.72  thf(l54_zfmisc_1, axiom,
% 54.52/54.72    (![A:$i,B:$i,C:$i,D:$i]:
% 54.52/54.72     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 54.52/54.72       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 54.52/54.72  thf('5', plain,
% 54.52/54.72      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 54.52/54.72         ((r2_hidden @ X35 @ X36)
% 54.52/54.72          | ~ (r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X38)))),
% 54.52/54.72      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.52/54.72  thf('6', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i]:
% 54.52/54.72         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 54.52/54.72          | (r2_hidden @ (sk_D_3 @ sk_A) @ X1))),
% 54.52/54.72      inference('sup-', [status(thm)], ['4', '5'])).
% 54.52/54.72  thf('7', plain, ((r2_hidden @ (sk_D_3 @ sk_A) @ sk_B)),
% 54.52/54.72      inference('sup-', [status(thm)], ['1', '6'])).
% 54.52/54.72  thf('8', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_4 @ sk_E_3))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf('9', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i]:
% 54.52/54.72         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 54.52/54.72          | (r2_hidden @ (sk_D_3 @ sk_A) @ X1))),
% 54.52/54.72      inference('sup-', [status(thm)], ['4', '5'])).
% 54.52/54.72  thf('10', plain, ((r2_hidden @ (sk_D_3 @ sk_A) @ sk_D_4)),
% 54.52/54.72      inference('sup-', [status(thm)], ['8', '9'])).
% 54.52/54.72  thf(d4_xboole_0, axiom,
% 54.52/54.72    (![A:$i,B:$i,C:$i]:
% 54.52/54.72     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 54.52/54.72       ( ![D:$i]:
% 54.52/54.72         ( ( r2_hidden @ D @ C ) <=>
% 54.52/54.72           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 54.52/54.72  thf('11', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.52/54.72         (~ (r2_hidden @ X0 @ X1)
% 54.52/54.72          | ~ (r2_hidden @ X0 @ X2)
% 54.52/54.72          | (r2_hidden @ X0 @ X3)
% 54.52/54.72          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 54.52/54.72      inference('cnf', [status(esa)], [d4_xboole_0])).
% 54.52/54.72  thf('12', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.52/54.72         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 54.52/54.72          | ~ (r2_hidden @ X0 @ X2)
% 54.52/54.72          | ~ (r2_hidden @ X0 @ X1))),
% 54.52/54.72      inference('simplify', [status(thm)], ['11'])).
% 54.52/54.72  thf('13', plain,
% 54.52/54.72      (![X0 : $i]:
% 54.52/54.72         (~ (r2_hidden @ (sk_D_3 @ sk_A) @ X0)
% 54.52/54.72          | (r2_hidden @ (sk_D_3 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_D_4)))),
% 54.52/54.72      inference('sup-', [status(thm)], ['10', '12'])).
% 54.52/54.72  thf('14', plain,
% 54.52/54.72      ((r2_hidden @ (sk_D_3 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_D_4))),
% 54.52/54.72      inference('sup-', [status(thm)], ['7', '13'])).
% 54.52/54.72  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf('16', plain,
% 54.52/54.72      (((k4_tarski @ (sk_D_3 @ sk_A) @ (sk_E_2 @ sk_A)) = (sk_A))),
% 54.52/54.72      inference('sup-', [status(thm)], ['2', '3'])).
% 54.52/54.72  thf('17', plain,
% 54.52/54.72      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 54.52/54.72         ((r2_hidden @ X37 @ X38)
% 54.52/54.72          | ~ (r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X38)))),
% 54.52/54.72      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.52/54.72  thf('18', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i]:
% 54.52/54.72         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 54.52/54.72          | (r2_hidden @ (sk_E_2 @ sk_A) @ X0))),
% 54.52/54.72      inference('sup-', [status(thm)], ['16', '17'])).
% 54.52/54.72  thf('19', plain, ((r2_hidden @ (sk_E_2 @ sk_A) @ sk_C)),
% 54.52/54.72      inference('sup-', [status(thm)], ['15', '18'])).
% 54.52/54.72  thf('20', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_4 @ sk_E_3))),
% 54.52/54.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.52/54.72  thf('21', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i]:
% 54.52/54.72         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 54.52/54.72          | (r2_hidden @ (sk_E_2 @ sk_A) @ X0))),
% 54.52/54.72      inference('sup-', [status(thm)], ['16', '17'])).
% 54.52/54.72  thf('22', plain, ((r2_hidden @ (sk_E_2 @ sk_A) @ sk_E_3)),
% 54.52/54.72      inference('sup-', [status(thm)], ['20', '21'])).
% 54.52/54.72  thf('23', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.52/54.72         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 54.52/54.72          | ~ (r2_hidden @ X0 @ X2)
% 54.52/54.72          | ~ (r2_hidden @ X0 @ X1))),
% 54.52/54.72      inference('simplify', [status(thm)], ['11'])).
% 54.52/54.72  thf('24', plain,
% 54.52/54.72      (![X0 : $i]:
% 54.52/54.72         (~ (r2_hidden @ (sk_E_2 @ sk_A) @ X0)
% 54.52/54.72          | (r2_hidden @ (sk_E_2 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_E_3)))),
% 54.52/54.72      inference('sup-', [status(thm)], ['22', '23'])).
% 54.52/54.72  thf('25', plain,
% 54.52/54.72      ((r2_hidden @ (sk_E_2 @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_E_3))),
% 54.52/54.72      inference('sup-', [status(thm)], ['19', '24'])).
% 54.52/54.72  thf('26', plain,
% 54.52/54.72      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 54.52/54.72         ((r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X39))
% 54.52/54.72          | ~ (r2_hidden @ X37 @ X39)
% 54.52/54.72          | ~ (r2_hidden @ X35 @ X36))),
% 54.52/54.72      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.52/54.72  thf('27', plain,
% 54.52/54.72      (![X0 : $i, X1 : $i]:
% 54.52/54.72         (~ (r2_hidden @ X1 @ X0)
% 54.52/54.72          | (r2_hidden @ (k4_tarski @ X1 @ (sk_E_2 @ sk_A)) @ 
% 54.52/54.72             (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_C @ sk_E_3))))),
% 54.52/54.72      inference('sup-', [status(thm)], ['25', '26'])).
% 54.52/54.72  thf('28', plain,
% 54.52/54.72      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_A) @ (sk_E_2 @ sk_A)) @ 
% 54.52/54.72        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_4) @ 
% 54.52/54.72         (k3_xboole_0 @ sk_C @ sk_E_3)))),
% 54.52/54.72      inference('sup-', [status(thm)], ['14', '27'])).
% 54.52/54.72  thf('29', plain,
% 54.52/54.72      (((k4_tarski @ (sk_D_3 @ sk_A) @ (sk_E_2 @ sk_A)) = (sk_A))),
% 54.52/54.72      inference('sup-', [status(thm)], ['2', '3'])).
% 54.52/54.72  thf('30', plain,
% 54.52/54.72      ((r2_hidden @ sk_A @ 
% 54.52/54.72        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_B @ sk_D_4) @ 
% 54.52/54.72         (k3_xboole_0 @ sk_C @ sk_E_3)))),
% 54.52/54.72      inference('demod', [status(thm)], ['28', '29'])).
% 54.52/54.72  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 54.52/54.72  
% 54.52/54.72  % SZS output end Refutation
% 54.52/54.72  
% 54.52/54.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
