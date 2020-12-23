%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QRpPLcs4wW

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   60 (  69 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  415 ( 519 expanded)
%              Number of equality atoms :   48 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('0',plain,(
    ! [X78: $i,X80: $i,X81: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X78 @ X80 ) @ X81 )
        = ( k1_tarski @ X78 ) )
      | ( X78 != X80 )
      | ( r2_hidden @ X78 @ X81 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('1',plain,(
    ! [X80: $i,X81: $i] :
      ( ( r2_hidden @ X80 @ X81 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X80 @ X80 ) @ X81 )
        = ( k1_tarski @ X80 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X50: $i] :
      ( ( k2_tarski @ X50 @ X50 )
      = ( k1_tarski @ X50 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X80: $i,X81: $i] :
      ( ( r2_hidden @ X80 @ X81 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X80 ) @ X81 )
        = ( k1_tarski @ X80 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X82: $i,X83: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X82 ) @ ( k2_tarski @ X82 @ X83 ) )
      = ( k1_tarski @ X82 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X50: $i] :
      ( ( k2_tarski @ X50 @ X50 )
      = ( k1_tarski @ X50 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X78: $i,X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X78 @ X79 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X78 @ X80 ) @ X79 )
       != ( k1_tarski @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
       != ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X41 != X43 )
      | ( r2_hidden @ X41 @ X42 )
      | ( X42
       != ( k2_tarski @ X43 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('25',plain,(
    ! [X40: $i,X43: $i] :
      ( r2_hidden @ X43 @ ( k2_tarski @ X43 @ X40 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
     != ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X50: $i] :
      ( ( k2_tarski @ X50 @ X50 )
      = ( k1_tarski @ X50 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X40: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X44 @ X42 )
      | ( X44 = X43 )
      | ( X44 = X40 )
      | ( X42
       != ( k2_tarski @ X43 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X40: $i,X43: $i,X44: $i] :
      ( ( X44 = X40 )
      | ( X44 = X43 )
      | ~ ( r2_hidden @ X44 @ ( k2_tarski @ X43 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QRpPLcs4wW
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:20:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 214 iterations in 0.100s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.54  thf(l38_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.54       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.37/0.54         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (![X78 : $i, X80 : $i, X81 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k2_tarski @ X78 @ X80) @ X81) = (k1_tarski @ X78))
% 0.37/0.54          | ((X78) != (X80))
% 0.37/0.54          | (r2_hidden @ X78 @ X81))),
% 0.37/0.54      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X80 : $i, X81 : $i]:
% 0.37/0.54         ((r2_hidden @ X80 @ X81)
% 0.37/0.54          | ((k4_xboole_0 @ (k2_tarski @ X80 @ X80) @ X81) = (k1_tarski @ X80)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.54  thf(t69_enumset1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('2', plain, (![X50 : $i]: ((k2_tarski @ X50 @ X50) = (k1_tarski @ X50))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X80 : $i, X81 : $i]:
% 0.37/0.54         ((r2_hidden @ X80 @ X81)
% 0.37/0.54          | ((k4_xboole_0 @ (k1_tarski @ X80) @ X81) = (k1_tarski @ X80)))),
% 0.37/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf(t28_zfmisc_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.37/0.54          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.37/0.54             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t19_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.37/0.54       ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X82 : $i, X83 : $i]:
% 0.37/0.54         ((k3_xboole_0 @ (k1_tarski @ X82) @ (k2_tarski @ X82 @ X83))
% 0.37/0.54           = (k1_tarski @ X82))),
% 0.37/0.54      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.37/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.54  thf(t17_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.37/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['5', '8'])).
% 0.37/0.54  thf(t1_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.54       ( r1_tarski @ A @ C ) ))).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X17 @ X18)
% 0.37/0.54          | ~ (r1_tarski @ X18 @ X19)
% 0.37/0.54          | (r1_tarski @ X17 @ X19))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.37/0.54          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['4', '11'])).
% 0.37/0.54  thf(t28_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X20 : $i, X21 : $i]:
% 0.37/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.37/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.37/0.54         = (k1_tarski @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.54  thf(t100_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X13 @ X14)
% 0.37/0.54           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.37/0.54         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      ((((k1_tarski @ sk_A)
% 0.37/0.54          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.37/0.54        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['3', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X50 : $i]: ((k2_tarski @ X50 @ X50) = (k1_tarski @ X50))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.54  thf('19', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X13 @ X14)
% 0.37/0.54           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X78 : $i, X79 : $i, X80 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X78 @ X79)
% 0.37/0.54          | ((k4_xboole_0 @ (k2_tarski @ X78 @ X80) @ X79) != (k1_tarski @ X78)))),
% 0.37/0.54      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))
% 0.37/0.54            != (k1_tarski @ X1))
% 0.37/0.54          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf(d2_tarski, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.54       ( ![D:$i]:
% 0.37/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.37/0.54         (((X41) != (X43))
% 0.37/0.54          | (r2_hidden @ X41 @ X42)
% 0.37/0.54          | ((X42) != (k2_tarski @ X43 @ X40)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X40 : $i, X43 : $i]: (r2_hidden @ X43 @ (k2_tarski @ X43 @ X40))),
% 0.37/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))
% 0.37/0.54           != (k1_tarski @ X1))),
% 0.37/0.54      inference('demod', [status(thm)], ['23', '25'])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k5_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.37/0.54           != (k1_tarski @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['18', '26'])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X50 : $i]: ((k2_tarski @ X50 @ X50) = (k1_tarski @ X50))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.54           != (k1_tarski @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.54  thf('30', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['17', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X40 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X44 @ X42)
% 0.37/0.54          | ((X44) = (X43))
% 0.37/0.54          | ((X44) = (X40))
% 0.37/0.54          | ((X42) != (k2_tarski @ X43 @ X40)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X40 : $i, X43 : $i, X44 : $i]:
% 0.37/0.54         (((X44) = (X40))
% 0.37/0.54          | ((X44) = (X43))
% 0.37/0.54          | ~ (r2_hidden @ X44 @ (k2_tarski @ X43 @ X40)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.54  thf('33', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['30', '32'])).
% 0.37/0.54  thf('34', plain, (((sk_A) != (sk_D_1))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('35', plain, (((sk_A) != (sk_C_1))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('36', plain, ($false),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['33', '34', '35'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
