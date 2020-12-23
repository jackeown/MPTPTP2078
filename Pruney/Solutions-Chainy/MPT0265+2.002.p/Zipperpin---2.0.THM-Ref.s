%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sy9OANJ7bU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:43 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 135 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  451 (1333 expanded)
%              Number of equality atoms :   59 ( 171 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t60_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( ( r2_hidden @ C @ B )
            & ( A != C ) )
          | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
            = ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( sk_A = sk_C ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X13 @ X15 ) @ X16 )
        = ( k1_tarski @ X13 ) )
      | ( X13 != X15 )
      | ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X15 ) @ X16 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

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
      ( ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_C ) @ sk_B ) )
   <= ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C @ sk_C ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C @ sk_C ) @ sk_B )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_C ) @ sk_B )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_C ),
    inference('simplify_reflect-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X13 @ X15 ) @ X16 )
        = ( k1_tarski @ X13 ) )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_tarski @ X18 ) )
        = ( k1_tarski @ X17 ) )
      | ( X17 = X18 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_C @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_C )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('42',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['26','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['25','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sy9OANJ7bU
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.48/1.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.48/1.66  % Solved by: fo/fo7.sh
% 1.48/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.48/1.66  % done 1738 iterations in 1.211s
% 1.48/1.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.48/1.66  % SZS output start Refutation
% 1.48/1.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.48/1.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.48/1.66  thf(sk_C_type, type, sk_C: $i).
% 1.48/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.48/1.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.48/1.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.48/1.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.48/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.48/1.66  thf(t60_zfmisc_1, conjecture,
% 1.48/1.66    (![A:$i,B:$i,C:$i]:
% 1.48/1.66     ( ( r2_hidden @ A @ B ) =>
% 1.48/1.66       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 1.48/1.66         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 1.48/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.48/1.66    (~( ![A:$i,B:$i,C:$i]:
% 1.48/1.66        ( ( r2_hidden @ A @ B ) =>
% 1.48/1.66          ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 1.48/1.66            ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ) )),
% 1.48/1.66    inference('cnf.neg', [status(esa)], [t60_zfmisc_1])).
% 1.48/1.66  thf('0', plain, ((~ (r2_hidden @ sk_C @ sk_B) | ((sk_A) = (sk_C)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('1', plain,
% 1.48/1.66      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 1.48/1.66      inference('split', [status(esa)], ['0'])).
% 1.48/1.66  thf('2', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('split', [status(esa)], ['0'])).
% 1.48/1.66  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('4', plain, (((r2_hidden @ sk_C @ sk_B)) <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('sup+', [status(thm)], ['2', '3'])).
% 1.48/1.66  thf(t69_enumset1, axiom,
% 1.48/1.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.48/1.66  thf('5', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 1.48/1.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.48/1.66  thf(l38_zfmisc_1, axiom,
% 1.48/1.66    (![A:$i,B:$i,C:$i]:
% 1.48/1.66     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 1.48/1.66       ( ( ~( r2_hidden @ A @ C ) ) & 
% 1.48/1.66         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 1.48/1.66  thf('6', plain,
% 1.48/1.66      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k2_tarski @ X13 @ X15) @ X16) = (k1_tarski @ X13))
% 1.48/1.66          | ((X13) != (X15))
% 1.48/1.66          | (r2_hidden @ X13 @ X16))),
% 1.48/1.66      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 1.48/1.66  thf('7', plain,
% 1.48/1.66      (![X15 : $i, X16 : $i]:
% 1.48/1.66         ((r2_hidden @ X15 @ X16)
% 1.48/1.66          | ((k4_xboole_0 @ (k2_tarski @ X15 @ X15) @ X16) = (k1_tarski @ X15)))),
% 1.48/1.66      inference('simplify', [status(thm)], ['6'])).
% 1.48/1.66  thf('8', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.48/1.66          | (r2_hidden @ X0 @ X1))),
% 1.48/1.66      inference('sup+', [status(thm)], ['5', '7'])).
% 1.48/1.66  thf(t48_xboole_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.48/1.66  thf('9', plain,
% 1.48/1.66      (![X6 : $i, X7 : $i]:
% 1.48/1.66         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 1.48/1.66           = (k3_xboole_0 @ X6 @ X7))),
% 1.48/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.48/1.66  thf('10', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.48/1.66          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.48/1.66      inference('sup+', [status(thm)], ['8', '9'])).
% 1.48/1.66  thf(d5_xboole_0, axiom,
% 1.48/1.66    (![A:$i,B:$i,C:$i]:
% 1.48/1.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.48/1.66       ( ![D:$i]:
% 1.48/1.66         ( ( r2_hidden @ D @ C ) <=>
% 1.48/1.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.48/1.66  thf('11', plain,
% 1.48/1.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.48/1.66         (~ (r2_hidden @ X4 @ X3)
% 1.48/1.66          | ~ (r2_hidden @ X4 @ X2)
% 1.48/1.66          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.48/1.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.48/1.66  thf('12', plain,
% 1.48/1.66      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.48/1.66         (~ (r2_hidden @ X4 @ X2)
% 1.48/1.66          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.48/1.66      inference('simplify', [status(thm)], ['11'])).
% 1.48/1.66  thf('13', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         (((k1_tarski @ X1) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.48/1.66          | ~ (r2_hidden @ X1 @ X0))),
% 1.48/1.66      inference('sup-', [status(thm)], ['10', '12'])).
% 1.48/1.66  thf('14', plain,
% 1.48/1.66      ((((k1_tarski @ sk_C) = (k3_xboole_0 @ (k1_tarski @ sk_C) @ sk_B)))
% 1.48/1.66         <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['4', '13'])).
% 1.48/1.66  thf('15', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('split', [status(esa)], ['0'])).
% 1.48/1.66  thf('16', plain,
% 1.48/1.66      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (k1_tarski @ sk_A))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('17', plain,
% 1.48/1.66      ((((k3_xboole_0 @ (k2_tarski @ sk_C @ sk_C) @ sk_B) != (k1_tarski @ sk_A)))
% 1.48/1.66         <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['15', '16'])).
% 1.48/1.66  thf('18', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('split', [status(esa)], ['0'])).
% 1.48/1.66  thf('19', plain,
% 1.48/1.66      ((((k3_xboole_0 @ (k2_tarski @ sk_C @ sk_C) @ sk_B) != (k1_tarski @ sk_C)))
% 1.48/1.66         <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('demod', [status(thm)], ['17', '18'])).
% 1.48/1.66  thf('20', plain,
% 1.48/1.66      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 1.48/1.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.48/1.66  thf('21', plain,
% 1.48/1.66      ((((k3_xboole_0 @ (k1_tarski @ sk_C) @ sk_B) != (k1_tarski @ sk_C)))
% 1.48/1.66         <= ((((sk_A) = (sk_C))))),
% 1.48/1.66      inference('demod', [status(thm)], ['19', '20'])).
% 1.48/1.66  thf('22', plain, (~ (((sk_A) = (sk_C)))),
% 1.48/1.66      inference('simplify_reflect-', [status(thm)], ['14', '21'])).
% 1.48/1.66  thf('23', plain, (~ ((r2_hidden @ sk_C @ sk_B)) | (((sk_A) = (sk_C)))),
% 1.48/1.66      inference('split', [status(esa)], ['0'])).
% 1.48/1.66  thf('24', plain, (~ ((r2_hidden @ sk_C @ sk_B))),
% 1.48/1.66      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 1.48/1.66  thf('25', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 1.48/1.66      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 1.48/1.66  thf('26', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('27', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('28', plain,
% 1.48/1.66      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k2_tarski @ X13 @ X15) @ X16) = (k1_tarski @ X13))
% 1.48/1.66          | ~ (r2_hidden @ X15 @ X16)
% 1.48/1.66          | (r2_hidden @ X13 @ X16))),
% 1.48/1.66      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 1.48/1.66  thf('29', plain,
% 1.48/1.66      (![X0 : $i]:
% 1.48/1.66         ((r2_hidden @ X0 @ sk_B)
% 1.48/1.66          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_B) = (k1_tarski @ X0)))),
% 1.48/1.66      inference('sup-', [status(thm)], ['27', '28'])).
% 1.48/1.66  thf('30', plain,
% 1.48/1.66      (![X6 : $i, X7 : $i]:
% 1.48/1.66         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 1.48/1.66           = (k3_xboole_0 @ X6 @ X7))),
% 1.48/1.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.48/1.66  thf('31', plain,
% 1.48/1.66      (![X0 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ (k1_tarski @ X0))
% 1.48/1.66            = (k3_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_B))
% 1.48/1.66          | (r2_hidden @ X0 @ sk_B))),
% 1.48/1.66      inference('sup+', [status(thm)], ['29', '30'])).
% 1.48/1.66  thf(commutativity_k2_tarski, axiom,
% 1.48/1.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.48/1.66  thf('32', plain,
% 1.48/1.66      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 1.48/1.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.48/1.66  thf(t23_zfmisc_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( ( A ) != ( B ) ) =>
% 1.48/1.66       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 1.48/1.66         ( k1_tarski @ A ) ) ))).
% 1.48/1.66  thf('33', plain,
% 1.48/1.66      (![X17 : $i, X18 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k1_tarski @ X18))
% 1.48/1.66            = (k1_tarski @ X17))
% 1.48/1.66          | ((X17) = (X18)))),
% 1.48/1.66      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 1.48/1.66  thf('34', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.48/1.66            = (k1_tarski @ X0))
% 1.48/1.66          | ((X0) = (X1)))),
% 1.48/1.66      inference('sup+', [status(thm)], ['32', '33'])).
% 1.48/1.66  thf('35', plain,
% 1.48/1.66      (![X0 : $i]:
% 1.48/1.66         (((k3_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_B) = (k1_tarski @ sk_A))
% 1.48/1.66          | (r2_hidden @ X0 @ sk_B)
% 1.48/1.66          | ((sk_A) = (X0)))),
% 1.48/1.66      inference('sup+', [status(thm)], ['31', '34'])).
% 1.48/1.66  thf('36', plain,
% 1.48/1.66      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (k1_tarski @ sk_A))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('37', plain,
% 1.48/1.66      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 1.48/1.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.48/1.66  thf('38', plain,
% 1.48/1.66      (((k3_xboole_0 @ (k2_tarski @ sk_C @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.48/1.66      inference('demod', [status(thm)], ['36', '37'])).
% 1.48/1.66  thf('39', plain,
% 1.48/1.66      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.48/1.66        | ((sk_A) = (sk_C))
% 1.48/1.66        | (r2_hidden @ sk_C @ sk_B))),
% 1.48/1.66      inference('sup-', [status(thm)], ['35', '38'])).
% 1.48/1.66  thf('40', plain, (((r2_hidden @ sk_C @ sk_B) | ((sk_A) = (sk_C)))),
% 1.48/1.66      inference('simplify', [status(thm)], ['39'])).
% 1.48/1.66  thf('41', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 1.48/1.66      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 1.48/1.66  thf('42', plain, (((sk_A) = (sk_C))),
% 1.48/1.66      inference('clc', [status(thm)], ['40', '41'])).
% 1.48/1.66  thf('43', plain, ((r2_hidden @ sk_C @ sk_B)),
% 1.48/1.66      inference('demod', [status(thm)], ['26', '42'])).
% 1.48/1.66  thf('44', plain, ($false), inference('demod', [status(thm)], ['25', '43'])).
% 1.48/1.66  
% 1.48/1.66  % SZS output end Refutation
% 1.48/1.66  
% 1.48/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
