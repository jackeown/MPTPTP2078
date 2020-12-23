%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j97JKm69xT

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  98 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  273 ( 889 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X7 ) @ ( sk_E @ X7 ) )
        = X7 )
      | ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('6',plain,
    ( ( k4_tarski @ ( sk_D @ sk_D_1 ) @ ( sk_E @ sk_D_1 ) )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('8',plain,
    ( ( k4_tarski @ ( sk_D @ sk_D_1 ) @ ( sk_E @ sk_D_1 ) )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( sk_E @ sk_D_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( sk_E @ sk_D_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ sk_B_1 )
      | ( sk_D_1
       != ( k4_tarski @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D_1
       != ( k4_tarski @ X0 @ ( sk_E @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('20',plain,
    ( ( k4_tarski @ ( sk_D @ sk_D_1 ) @ ( sk_E @ sk_D_1 ) )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_D_1 != sk_D_1 ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j97JKm69xT
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 62 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(t65_subset_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ~( ( r2_hidden @ D @ C ) & 
% 0.21/0.48          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.21/0.48          ( ![E:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.48              ( ![F:$i]:
% 0.21/0.48                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ~( ( r2_hidden @ D @ C ) & 
% 0.21/0.48             ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.21/0.48             ( ![E:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.48                 ( ![F:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                     ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t65_subset_1])).
% 0.21/0.48  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.48          | (r2_hidden @ X3 @ X5)
% 0.21/0.48          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf(l139_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.48          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((k4_tarski @ (sk_D @ X7) @ (sk_E @ X7)) = (X7))
% 0.21/0.48          | ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((k4_tarski @ (sk_D @ sk_D_1) @ (sk_E @ sk_D_1)) = (sk_D_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((k4_tarski @ (sk_D @ sk_D_1) @ (sk_E @ sk_D_1)) = (sk_D_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(l54_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         ((r2_hidden @ X12 @ X13)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.48          | (r2_hidden @ (sk_E @ sk_D_1) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((r2_hidden @ (sk_E @ sk_D_1) @ sk_B_1)),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.48  thf(d2_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X15 @ X16)
% 0.21/0.48          | (m1_subset_1 @ X15 @ X16)
% 0.21/0.48          | (v1_xboole_0 @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, ((m1_subset_1 @ (sk_E @ sk_D_1) @ sk_B_1)),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X18 @ sk_B_1)
% 0.21/0.48          | ((sk_D_1) != (k4_tarski @ X19 @ X18))
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | ((sk_D_1) != (k4_tarski @ X0 @ (sk_E @ sk_D_1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((sk_D_1) != (sk_D_1)) | ~ (m1_subset_1 @ (sk_D @ sk_D_1) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '17'])).
% 0.21/0.48  thf('19', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((k4_tarski @ (sk_D @ sk_D_1) @ (sk_E @ sk_D_1)) = (sk_D_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         ((r2_hidden @ X10 @ X11)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.48          | (r2_hidden @ (sk_D @ sk_D_1) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((r2_hidden @ (sk_D @ sk_D_1) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('25', plain, ((m1_subset_1 @ (sk_D @ sk_D_1) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain, (((sk_D_1) != (sk_D_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '25'])).
% 0.21/0.48  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
