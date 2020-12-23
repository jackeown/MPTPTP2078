%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rGiqCz43bn

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:45 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  282 ( 460 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k1_tarski @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X25 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ X0 ) ) )
      | ( sk_C_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X24 )
      | ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ~ ( r2_hidden @ X24 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( sk_C_1
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('27',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['20','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rGiqCz43bn
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 305 iterations in 0.170s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.63  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.43/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.63  thf(t13_mcart_1, conjecture,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.43/0.63       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.43/0.63         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.63        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.43/0.63          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.43/0.63            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ (k1_tarski @ sk_C_1)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(t10_mcart_1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.43/0.63       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.43/0.63         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.63         ((r2_hidden @ (k2_mcart_1 @ X26) @ X28)
% 0.43/0.63          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.43/0.63  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.63  thf(d3_tarski, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      (![X1 : $i, X3 : $i]:
% 0.43/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('4', plain,
% 0.43/0.63      (![X1 : $i, X3 : $i]:
% 0.43/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('5', plain,
% 0.43/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.63  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.43/0.63  thf(l1_zfmisc_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      (![X14 : $i, X15 : $i]:
% 0.43/0.63         ((r2_hidden @ X14 @ X15) | ~ (r1_tarski @ (k1_tarski @ X14) @ X15))),
% 0.43/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.63  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.63  thf(t64_zfmisc_1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.43/0.63       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.43/0.63         ((r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X25)))
% 0.43/0.63          | ((X22) = (X25))
% 0.43/0.63          | ~ (r2_hidden @ X22 @ X23))),
% 0.43/0.63      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.43/0.63  thf('10', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (((X0) = (X1))
% 0.43/0.63          | (r2_hidden @ X0 @ 
% 0.43/0.63             (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.63  thf('11', plain,
% 0.43/0.63      (![X14 : $i, X16 : $i]:
% 0.43/0.63         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.43/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.63  thf('12', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (((X1) = (X0))
% 0.43/0.63          | (r1_tarski @ (k1_tarski @ X1) @ 
% 0.43/0.63             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.63  thf('13', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.63          | (r2_hidden @ X0 @ X2)
% 0.43/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('14', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (((X1) = (X0))
% 0.43/0.63          | (r2_hidden @ X2 @ 
% 0.43/0.63             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.43/0.63          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.63  thf('15', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.43/0.63           (k4_xboole_0 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ X0)))
% 0.43/0.63          | ((sk_C_1) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['2', '14'])).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.63         (((X22) != (X24))
% 0.43/0.63          | ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24))))),
% 0.43/0.63      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X23 : $i, X24 : $i]:
% 0.43/0.63         ~ (r2_hidden @ X24 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.43/0.63  thf('18', plain, (((sk_C_1) = (k2_mcart_1 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['15', '17'])).
% 0.43/0.63  thf('19', plain,
% 0.43/0.63      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)
% 0.43/0.63        | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.43/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.43/0.63      inference('split', [status(esa)], ['19'])).
% 0.43/0.63  thf('21', plain,
% 0.43/0.63      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ (k1_tarski @ sk_C_1)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.63         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.43/0.63          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.43/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.43/0.63  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)),
% 0.43/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))
% 0.43/0.63         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)))),
% 0.43/0.63      inference('split', [status(esa)], ['19'])).
% 0.43/0.63  thf('25', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.63  thf('26', plain,
% 0.43/0.63      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.43/0.63       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.43/0.63      inference('split', [status(esa)], ['19'])).
% 0.43/0.63  thf('27', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.43/0.63  thf('28', plain, (((k2_mcart_1 @ sk_A) != (sk_C_1))),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['20', '27'])).
% 0.43/0.63  thf('29', plain, ($false),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['18', '28'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
