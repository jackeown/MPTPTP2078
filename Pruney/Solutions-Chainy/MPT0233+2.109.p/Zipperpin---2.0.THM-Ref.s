%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQVcq9E8bE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  67 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  410 ( 484 expanded)
%              Number of equality atoms :   54 (  65 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('0',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X45 @ X47 ) @ X48 )
        = ( k1_tarski @ X45 ) )
      | ( X45 != X47 )
      | ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X47 @ X47 ) @ X48 )
        = ( k1_tarski @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
        = ( k1_tarski @ X47 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X52 ) )
      | ( X51
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,(
    ! [X49: $i,X52: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X52 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('21',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54 != X53 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ ( k1_tarski @ X53 ) )
       != ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('22',plain,(
    ! [X53: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X53 ) )
     != ( k1_tarski @ X53 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X53: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X53 ) ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['20','27'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ( X15 = X14 )
      | ( X15 = X11 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('30',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( X15 = X11 )
      | ( X15 = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQVcq9E8bE
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 101 iterations in 0.041s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(l38_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.49         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ (k2_tarski @ X45 @ X47) @ X48) = (k1_tarski @ X45))
% 0.21/0.49          | ((X45) != (X47))
% 0.21/0.49          | (r2_hidden @ X45 @ X48))),
% 0.21/0.49      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X47 : $i, X48 : $i]:
% 0.21/0.49         ((r2_hidden @ X47 @ X48)
% 0.21/0.49          | ((k4_xboole_0 @ (k2_tarski @ X47 @ X47) @ X48) = (k1_tarski @ X47)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('2', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X47 : $i, X48 : $i]:
% 0.21/0.49         ((r2_hidden @ X47 @ X48)
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X47) @ X48) = (k1_tarski @ X47)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(l45_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.49            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.21/0.49         ((r1_tarski @ X51 @ (k2_tarski @ X49 @ X52))
% 0.21/0.49          | ((X51) != (k1_tarski @ X49)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X49 : $i, X52 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X52))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf(t28_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.49          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.49             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.21/0.49         = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf(t18_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.49          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.21/0.49         = (k1_tarski @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.21/0.49         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf(t92_xboole_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.21/0.49         = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.49        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '19'])).
% 0.21/0.49  thf(t20_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49         ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ( A ) != ( B ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X53 : $i, X54 : $i]:
% 0.21/0.49         (((X54) != (X53))
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X54) @ (k1_tarski @ X53))
% 0.21/0.49              != (k1_tarski @ X54)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X53 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X53))
% 0.21/0.49           != (k1_tarski @ X53))),
% 0.21/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.49  thf('23', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.49           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.49  thf('27', plain, (![X53 : $i]: ((k1_xboole_0) != (k1_tarski @ X53))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.21/0.49  thf('28', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['20', '27'])).
% 0.21/0.49  thf(d2_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X15 @ X13)
% 0.21/0.49          | ((X15) = (X14))
% 0.21/0.49          | ((X15) = (X11))
% 0.21/0.49          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X15) = (X11))
% 0.21/0.49          | ((X15) = (X14))
% 0.21/0.49          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.49  thf('31', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.49  thf('32', plain, (((sk_A) != (sk_D_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, (((sk_A) != (sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32', '33'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
