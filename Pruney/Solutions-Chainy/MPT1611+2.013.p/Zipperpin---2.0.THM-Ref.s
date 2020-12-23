%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnJZDjpcYx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  75 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  303 ( 366 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X33: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X33: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X48 ) @ X48 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = ( k3_tarski @ X48 ) )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X48: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = ( k3_tarski @ X48 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X48 ) @ X48 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( ( k3_yellow_1 @ X49 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('12',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X36 @ X37 ) @ ( k9_setfam_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k9_setfam_1 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('30',plain,(
    ! [X47: $i] :
      ( ( k9_setfam_1 @ X47 )
      = ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('31',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnJZDjpcYx
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 45 iterations in 0.014s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.49  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t19_yellow_1, conjecture,
% 0.21/0.49    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.21/0.49  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t99_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.49  thf('1', plain, (![X33 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X33)) = (X33))),
% 0.21/0.49      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.49  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('2', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('3', plain, (![X33 : $i]: ((k3_tarski @ (k9_setfam_1 @ X33)) = (X33))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t14_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.49         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X48 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k3_tarski @ X48) @ X48)
% 0.21/0.49          | ((k4_yellow_0 @ (k2_yellow_1 @ X48)) = (k3_tarski @ X48))
% 0.21/0.49          | (v1_xboole_0 @ X48))),
% 0.21/0.49      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X48 : $i]:
% 0.21/0.49         (((k4_yellow_0 @ (k2_yellow_1 @ X48)) = (k3_tarski @ X48))
% 0.21/0.49          | ~ (r2_hidden @ (k3_tarski @ X48) @ X48))),
% 0.21/0.49      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.49          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.49              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf(t4_yellow_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X49 : $i]: ((k3_yellow_1 @ X49) = (k2_yellow_1 @ (k9_setfam_1 @ X49)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.49  thf('9', plain, (![X33 : $i]: ((k3_tarski @ (k9_setfam_1 @ X33)) = (X33))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.49          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.49  thf(t4_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf('12', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(dt_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X36 : $i, X37 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))
% 0.21/0.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.49  thf('15', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('16', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X36 : $i, X37 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_subset_1 @ X36 @ X37) @ (k9_setfam_1 @ X36))
% 0.21/0.49          | ~ (m1_subset_1 @ X37 @ (k9_setfam_1 @ X36)))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k9_setfam_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(d5_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X34 : $i, X35 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.21/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.49  thf('21', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X34 : $i, X35 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.21/0.49          | ~ (m1_subset_1 @ X35 @ (k9_setfam_1 @ X34)))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf(t3_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('24', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.49  thf('25', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '25'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X42 : $i, X43 : $i]:
% 0.21/0.49         ((r2_hidden @ X42 @ X43)
% 0.21/0.49          | (v1_xboole_0 @ X43)
% 0.21/0.49          | ~ (m1_subset_1 @ X42 @ X43))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.49          | (r2_hidden @ X0 @ (k9_setfam_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(fc1_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('29', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.49  thf('30', plain, (![X47 : $i]: ((k9_setfam_1 @ X47) = (k1_zfmisc_1 @ X47))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('31', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X38))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.49      inference('clc', [status(thm)], ['28', '31'])).
% 0.21/0.49  thf('33', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '32'])).
% 0.21/0.49  thf('34', plain, (((sk_A) != (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '33'])).
% 0.21/0.49  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
