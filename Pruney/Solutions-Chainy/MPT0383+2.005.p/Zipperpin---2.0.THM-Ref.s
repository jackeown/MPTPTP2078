%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.75dGixfO0o

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 119 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  311 (1079 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t65_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r2_hidden @ D @ C )
          & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ A )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( D
                   != ( k4_tarski @ E @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_D_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X11 ) @ ( sk_E @ X11 ) )
        = X11 )
      | ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('9',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_D_2 ) @ ( sk_E @ sk_D_2 ) )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('11',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_D_2 ) @ ( sk_E @ sk_D_2 ) )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_D_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_E @ sk_D_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B_1 )
      | ( sk_D_2
       != ( k4_tarski @ X23 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D_2
       != ( k4_tarski @ X0 @ ( sk_E @ sk_D_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('23',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_D_2 ) @ ( sk_E @ sk_D_2 ) )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D_1 @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_D_2 != sk_D_2 ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.75dGixfO0o
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 176 iterations in 0.068s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.53  thf(t65_subset_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ~( ( r2_hidden @ D @ C ) & 
% 0.21/0.53          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.21/0.53          ( ![E:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.53              ( ![F:$i]:
% 0.21/0.53                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ~( ( r2_hidden @ D @ C ) & 
% 0.21/0.53             ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.21/0.53             ( ![E:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.53                 ( ![F:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.53                     ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t65_subset_1])).
% 0.21/0.53  thf('0', plain, ((r2_hidden @ sk_D_2 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(d4_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.53          | (r2_hidden @ X7 @ X5)
% 0.21/0.53          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.53         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_C)
% 0.21/0.53          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('7', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf(l139_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.53          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (((k4_tarski @ (sk_D_1 @ X11) @ (sk_E @ X11)) = (X11))
% 0.21/0.53          | ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((k4_tarski @ (sk_D_1 @ sk_D_2) @ (sk_E @ sk_D_2)) = (sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((k4_tarski @ (sk_D_1 @ sk_D_2) @ (sk_E @ sk_D_2)) = (sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf(l54_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         ((r2_hidden @ X16 @ X17)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.53          | (r2_hidden @ (sk_E @ sk_D_2) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((r2_hidden @ (sk_E @ sk_D_2) @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf(d2_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X19 @ X20)
% 0.21/0.53          | (m1_subset_1 @ X19 @ X20)
% 0.21/0.53          | (v1_xboole_0 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.53  thf(d1_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.21/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((m1_subset_1 @ (sk_E @ sk_D_2) @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X22 @ sk_B_1)
% 0.21/0.53          | ((sk_D_2) != (k4_tarski @ X23 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.53          | ((sk_D_2) != (k4_tarski @ X0 @ (sk_E @ sk_D_2))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((sk_D_2) != (sk_D_2)) | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '20'])).
% 0.21/0.53  thf('22', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((k4_tarski @ (sk_D_1 @ sk_D_2) @ (sk_E @ sk_D_2)) = (sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         ((r2_hidden @ X14 @ X15)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ sk_D_2) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, ((r2_hidden @ (sk_D_1 @ sk_D_2) @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.21/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('28', plain, ((m1_subset_1 @ (sk_D_1 @ sk_D_2) @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, (((sk_D_2) != (sk_D_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '28'])).
% 0.21/0.53  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
