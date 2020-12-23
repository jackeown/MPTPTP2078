%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XeQkdoUB0o

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  446 ( 856 expanded)
%              Number of equality atoms :   53 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X42 @ X41 ) @ X41 )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
        = ( k1_tarski @ X34 ) )
      | ( X34 = X35 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 != X33 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) )
     != ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['13'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X33: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X33 ) ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['6','21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X23 != X22 )
      | ( r2_hidden @ X23 @ X24 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X22: $i] :
      ( r2_hidden @ X22 @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( sk_C_1 @ X42 @ X41 ) )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X33: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X33 ) ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XeQkdoUB0o
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 167 iterations in 0.132s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.63  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(t11_setfam_1, conjecture,
% 0.38/0.63    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.38/0.63  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(t6_setfam_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.38/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (![X41 : $i, X42 : $i]:
% 0.38/0.63         (((X41) = (k1_xboole_0))
% 0.38/0.63          | (r2_hidden @ (sk_C_1 @ X42 @ X41) @ X41)
% 0.38/0.63          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.38/0.63  thf(t20_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.63         ( k1_tarski @ A ) ) <=>
% 0.38/0.63       ( ( A ) != ( B ) ) ))).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X34 : $i, X35 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.38/0.63            = (k1_tarski @ X34))
% 0.38/0.63          | ((X34) = (X35)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.63  thf(t65_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.38/0.63       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      (![X36 : $i, X37 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X36 @ X37)
% 0.38/0.63          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.38/0.63          | ((X0) = (X1))
% 0.38/0.63          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.63  thf('5', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.63          | ((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['1', '5'])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (![X33 : $i, X34 : $i]:
% 0.38/0.63         (((X34) != (X33))
% 0.38/0.63          | ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X33))
% 0.38/0.63              != (k1_tarski @ X34)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X33 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))
% 0.38/0.63           != (k1_tarski @ X33))),
% 0.38/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.63  thf(d5_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.63       ( ![D:$i]:
% 0.38/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.38/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.63  thf(t3_boole, axiom,
% 0.38/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.63  thf('10', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.63          | ~ (r2_hidden @ X4 @ X2)
% 0.38/0.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.63          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.63  thf('13', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['10', '12'])).
% 0.38/0.63  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.63      inference('condensation', [status(thm)], ['13'])).
% 0.38/0.63  thf('15', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['9', '14'])).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.38/0.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.63          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.38/0.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.38/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 0.38/0.63          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.38/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.38/0.63          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.63  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.63      inference('condensation', [status(thm)], ['13'])).
% 0.38/0.63  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.63      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('21', plain, (![X33 : $i]: ((k1_xboole_0) != (k1_tarski @ X33))),
% 0.38/0.63      inference('demod', [status(thm)], ['8', '20'])).
% 0.38/0.63  thf('22', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0)))
% 0.38/0.63          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('clc', [status(thm)], ['6', '21'])).
% 0.38/0.63  thf(d1_tarski, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.63  thf('23', plain,
% 0.38/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.63         (((X23) != (X22))
% 0.38/0.63          | (r2_hidden @ X23 @ X24)
% 0.38/0.63          | ((X24) != (k1_tarski @ X22)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.63  thf('24', plain, (![X22 : $i]: (r2_hidden @ X22 @ (k1_tarski @ X22))),
% 0.38/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.63  thf(t4_setfam_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.38/0.63  thf('25', plain,
% 0.38/0.63      (![X39 : $i, X40 : $i]:
% 0.38/0.63         ((r1_tarski @ (k1_setfam_1 @ X39) @ X40) | ~ (r2_hidden @ X40 @ X39))),
% 0.38/0.63      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.38/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.63  thf(d10_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (![X6 : $i, X8 : $i]:
% 0.38/0.63         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.38/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.63  thf('28', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((X0) = (sk_C_1 @ X0 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['22', '28'])).
% 0.38/0.63  thf('30', plain,
% 0.38/0.63      (![X41 : $i, X42 : $i]:
% 0.38/0.63         (((X41) = (k1_xboole_0))
% 0.38/0.63          | ~ (r1_tarski @ X42 @ (sk_C_1 @ X42 @ X41))
% 0.38/0.63          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (r1_tarski @ X0 @ X0)
% 0.38/0.63          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.63  thf('32', plain,
% 0.38/0.63      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.63  thf('33', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.38/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.63  thf('34', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.63      inference('demod', [status(thm)], ['31', '33'])).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.38/0.63          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.63          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('clc', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('37', plain, (![X33 : $i]: ((k1_xboole_0) != (k1_tarski @ X33))),
% 0.38/0.63      inference('demod', [status(thm)], ['8', '20'])).
% 0.38/0.63  thf('38', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.38/0.63      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.63  thf('39', plain, (((sk_A) != (sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['0', '38'])).
% 0.38/0.63  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
