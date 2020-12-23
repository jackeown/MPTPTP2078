%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sKbBD9gdpj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  390 ( 644 expanded)
%              Number of equality atoms :   46 (  76 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X26 )
        = ( k2_tarski @ X23 @ X25 ) )
      | ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['13','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sKbBD9gdpj
% 0.13/0.38  % Computer   : n023.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 20:47:06 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.92/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.12  % Solved by: fo/fo7.sh
% 0.92/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.12  % done 1969 iterations in 0.639s
% 0.92/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.12  % SZS output start Refutation
% 0.92/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.92/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.92/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.92/1.12  thf(t144_zfmisc_1, conjecture,
% 0.92/1.12    (![A:$i,B:$i,C:$i]:
% 0.92/1.12     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.92/1.12          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.92/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.12        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.92/1.12             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.92/1.12    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.92/1.12  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.92/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.12  thf(t72_zfmisc_1, axiom,
% 0.92/1.12    (![A:$i,B:$i,C:$i]:
% 0.92/1.12     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.92/1.12       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.92/1.12  thf('1', plain,
% 0.92/1.12      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.92/1.12         (((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X26)
% 0.92/1.12            = (k2_tarski @ X23 @ X25))
% 0.92/1.12          | (r2_hidden @ X25 @ X26)
% 0.92/1.12          | (r2_hidden @ X23 @ X26))),
% 0.92/1.12      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.92/1.12  thf(t49_xboole_1, axiom,
% 0.92/1.12    (![A:$i,B:$i,C:$i]:
% 0.92/1.12     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.92/1.12       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.92/1.12  thf('2', plain,
% 0.92/1.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.92/1.12         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.12           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.92/1.12      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.92/1.12  thf(d10_xboole_0, axiom,
% 0.92/1.12    (![A:$i,B:$i]:
% 0.92/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.12  thf('3', plain,
% 0.92/1.12      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.92/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.12  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.92/1.12      inference('simplify', [status(thm)], ['3'])).
% 0.92/1.12  thf(l32_xboole_1, axiom,
% 0.92/1.12    (![A:$i,B:$i]:
% 0.92/1.12     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.92/1.12  thf('5', plain,
% 0.92/1.12      (![X5 : $i, X7 : $i]:
% 0.92/1.12         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.92/1.12      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.92/1.12  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.92/1.12  thf('7', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]:
% 0.92/1.12         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.92/1.12           = (k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['2', '6'])).
% 0.92/1.12  thf(commutativity_k3_xboole_0, axiom,
% 0.92/1.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.92/1.12  thf('8', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.12  thf(t47_xboole_1, axiom,
% 0.92/1.12    (![A:$i,B:$i]:
% 0.92/1.12     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.92/1.12  thf('9', plain,
% 0.92/1.12      (![X11 : $i, X12 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.92/1.12           = (k4_xboole_0 @ X11 @ X12))),
% 0.92/1.12      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.92/1.12  thf('10', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.92/1.12           = (k4_xboole_0 @ X0 @ X1))),
% 0.92/1.12      inference('sup+', [status(thm)], ['8', '9'])).
% 0.92/1.12  thf('11', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]:
% 0.92/1.12         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.92/1.12      inference('demod', [status(thm)], ['7', '10'])).
% 0.92/1.12  thf(t100_xboole_1, axiom,
% 0.92/1.12    (![A:$i,B:$i]:
% 0.92/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.92/1.12  thf('12', plain,
% 0.92/1.12      (![X8 : $i, X9 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X8 @ X9)
% 0.92/1.12           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.92/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.12  thf('13', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.92/1.12           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['11', '12'])).
% 0.92/1.12  thf(t3_boole, axiom,
% 0.92/1.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.92/1.12  thf('14', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.92/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.12  thf(t48_xboole_1, axiom,
% 0.92/1.12    (![A:$i,B:$i]:
% 0.92/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.92/1.12  thf('15', plain,
% 0.92/1.12      (![X13 : $i, X14 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.92/1.12           = (k3_xboole_0 @ X13 @ X14))),
% 0.92/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.12  thf('16', plain,
% 0.92/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['14', '15'])).
% 0.92/1.12  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.92/1.12  thf('18', plain,
% 0.92/1.12      (![X13 : $i, X14 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.92/1.12           = (k3_xboole_0 @ X13 @ X14))),
% 0.92/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.12  thf('19', plain,
% 0.92/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['17', '18'])).
% 0.92/1.12  thf('20', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.92/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.12  thf('21', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.92/1.12      inference('demod', [status(thm)], ['19', '20'])).
% 0.92/1.12  thf('22', plain,
% 0.92/1.12      (![X8 : $i, X9 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X8 @ X9)
% 0.92/1.12           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.92/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.12  thf('23', plain,
% 0.92/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['21', '22'])).
% 0.92/1.12  thf('24', plain,
% 0.92/1.12      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.92/1.12      inference('demod', [status(thm)], ['16', '23'])).
% 0.92/1.12  thf('25', plain,
% 0.92/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['21', '22'])).
% 0.92/1.12  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.92/1.12  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['25', '26'])).
% 0.92/1.12  thf('28', plain,
% 0.92/1.12      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['24', '27'])).
% 0.92/1.12  thf('29', plain,
% 0.92/1.12      (![X8 : $i, X9 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X8 @ X9)
% 0.92/1.12           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.92/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.12  thf('30', plain,
% 0.92/1.12      (![X0 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['28', '29'])).
% 0.92/1.12  thf('31', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.92/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.12  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.92/1.12      inference('sup+', [status(thm)], ['30', '31'])).
% 0.92/1.12  thf('33', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i]:
% 0.92/1.12         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.92/1.12      inference('demod', [status(thm)], ['13', '32'])).
% 0.92/1.12  thf('34', plain,
% 0.92/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.12         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 0.92/1.12          | (r2_hidden @ X1 @ X2)
% 0.92/1.12          | (r2_hidden @ X0 @ X2))),
% 0.92/1.12      inference('sup+', [status(thm)], ['1', '33'])).
% 0.92/1.12  thf('35', plain,
% 0.92/1.12      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.92/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.12  thf('36', plain,
% 0.92/1.12      ((((sk_C) != (sk_C))
% 0.92/1.12        | (r2_hidden @ sk_B @ sk_C)
% 0.92/1.12        | (r2_hidden @ sk_A @ sk_C))),
% 0.92/1.12      inference('sup-', [status(thm)], ['34', '35'])).
% 0.92/1.12  thf('37', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.92/1.12      inference('simplify', [status(thm)], ['36'])).
% 0.92/1.12  thf('38', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.92/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.12  thf('39', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.92/1.12      inference('clc', [status(thm)], ['37', '38'])).
% 0.92/1.12  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.92/1.12  
% 0.92/1.12  % SZS output end Refutation
% 0.92/1.12  
% 0.92/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
