%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J5C3WXXUE9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 161 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  354 (1094 expanded)
%              Number of equality atoms :   39 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
        = ( k1_tarski @ X43 ) )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t116_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t116_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X45 ) @ ( k2_tarski @ X45 @ X46 ) )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48 != X47 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X47 ) )
       != ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('28',plain,(
    ! [X47: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X47 ) )
     != ( k1_tarski @ X47 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('37',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J5C3WXXUE9
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 61 iterations in 0.032s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(t55_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ A @ C ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l31_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.49       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X43 : $i, X44 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X44 @ (k1_tarski @ X43)) = (k1_tarski @ X43))
% 0.20/0.49          | ~ (r2_hidden @ X43 @ X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d7_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(t116_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.49       ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.20/0.49           = (k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t116_xboole_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k3_xboole_0 @ sk_C @ X0))
% 0.20/0.49           = (k3_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.49              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('13', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k3_xboole_0 @ sk_C @ X0))
% 0.20/0.49           = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49             (k3_xboole_0 @ sk_C @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k3_xboole_0 @ sk_C @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.49         = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf(t19_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.49       ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X45 : $i, X46 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k1_tarski @ X45) @ (k2_tarski @ X45 @ X46))
% 0.20/0.49           = (k1_tarski @ X45))),
% 0.20/0.49      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.49  thf('26', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf(t20_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ( A ) != ( B ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X47 : $i, X48 : $i]:
% 0.20/0.49         (((X48) != (X47))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X47))
% 0.20/0.49              != (k1_tarski @ X48)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X47 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X47))
% 0.20/0.49           != (k1_tarski @ X47))),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.49  thf('30', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.49           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.49           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf(t92_xboole_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('34', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('37', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '35', '36'])).
% 0.20/0.49  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
