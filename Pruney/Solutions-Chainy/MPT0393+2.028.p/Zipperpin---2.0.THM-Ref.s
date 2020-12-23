%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FQBZnHmZ19

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 186 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  423 (1385 expanded)
%              Number of equality atoms :   51 ( 167 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X21 ) @ X21 )
      | ( r1_tarski @ X22 @ ( k1_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
        = ( k1_tarski @ X15 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X19 )
      | ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 != X14 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X14 ) )
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) )
     != ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X14 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X18 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_C @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X14 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_C @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X14 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_setfam_1 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( sk_C_1 @ X22 @ X21 ) )
      | ( r1_tarski @ X22 @ ( k1_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X14 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FQBZnHmZ19
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 158 iterations in 0.073s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.54  thf(t11_setfam_1, conjecture,
% 0.37/0.54    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.37/0.54  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t6_setfam_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.37/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X21 : $i, X22 : $i]:
% 0.37/0.54         (((X21) = (k1_xboole_0))
% 0.37/0.54          | (r2_hidden @ (sk_C_1 @ X22 @ X21) @ X21)
% 0.37/0.54          | (r1_tarski @ X22 @ (k1_setfam_1 @ X21)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.37/0.54  thf(t20_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.54         ( k1_tarski @ A ) ) <=>
% 0.37/0.54       ( ( A ) != ( B ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16))
% 0.37/0.54            = (k1_tarski @ X15))
% 0.37/0.54          | ((X15) = (X16)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.54  thf(t64_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.54       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (((X17) != (X19))
% 0.37/0.54          | ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19))))),
% 0.37/0.54      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.54          | ((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '5'])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]:
% 0.37/0.54         (((X15) != (X14))
% 0.37/0.54          | ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X14))
% 0.37/0.54              != (k1_tarski @ X15)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X14 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))
% 0.37/0.54           != (k1_tarski @ X14))),
% 0.37/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.54  thf(d10_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.54  thf(l32_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X5 : $i, X7 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.54  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.54  thf('13', plain, (![X14 : $i]: ((k1_xboole_0) != (k1_tarski @ X14))),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '12'])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0)))
% 0.37/0.54          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('clc', [status(thm)], ['6', '13'])).
% 0.37/0.54  thf('15', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.54  thf(t2_tarski, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.54       ( ( A ) = ( B ) ) ))).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (X0))
% 0.37/0.54          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.37/0.54          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.54  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X18 @ (k1_tarski @ X19)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.54  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.54          | ((X0) = (sk_C @ k1_xboole_0 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf('23', plain, (![X14 : $i]: ((k1_xboole_0) != (k1_tarski @ X14))),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '12'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X0 : $i]: ((X0) = (sk_C @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.54  thf('27', plain, (![X14 : $i]: ((k1_xboole_0) != (k1_tarski @ X14))),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '12'])).
% 0.37/0.54  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.37/0.54  thf(t8_setfam_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.37/0.54       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X23 @ X24)
% 0.37/0.54          | ~ (r1_tarski @ X23 @ X25)
% 0.37/0.54          | (r1_tarski @ (k1_setfam_1 @ X24) @ X25))),
% 0.37/0.54      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.37/0.54          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.37/0.54      inference('sup-', [status(thm)], ['15', '30'])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X2 : $i, X4 : $i]:
% 0.37/0.54         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((X0) = (sk_C_1 @ X0 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '33'])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X21 : $i, X22 : $i]:
% 0.37/0.54         (((X21) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X22 @ (sk_C_1 @ X22 @ X21))
% 0.37/0.54          | (r1_tarski @ X22 @ (k1_setfam_1 @ X21)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X0 @ X0)
% 0.37/0.54          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.54  thf('37', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.37/0.54          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.54          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.37/0.54  thf('41', plain, (![X14 : $i]: ((k1_xboole_0) != (k1_tarski @ X14))),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '12'])).
% 0.37/0.54  thf('42', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain, (((sk_A) != (sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '42'])).
% 0.37/0.54  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
