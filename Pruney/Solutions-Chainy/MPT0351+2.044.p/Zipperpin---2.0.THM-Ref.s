%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3jyinnD6vD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  370 ( 734 expanded)
%              Number of equality atoms :   29 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('22',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','22'])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3jyinnD6vD
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 107 iterations in 0.074s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(dt_k2_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('1', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('2', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t28_subset_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.21/0.52  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.21/0.52          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf(d3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.21/0.52         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.52          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.21/0.52         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.52          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.52          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.52          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['7'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.52      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.52          | (r2_hidden @ X12 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.21/0.52         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))
% 0.21/0.52        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 0.21/0.52        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 0.21/0.52        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X0 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf('22', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.21/0.52         != (k2_subset_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('26', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('27', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.52  thf('28', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['23', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
