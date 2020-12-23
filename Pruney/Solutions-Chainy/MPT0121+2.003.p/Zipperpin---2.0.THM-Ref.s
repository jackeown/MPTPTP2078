%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.akmT4puoWe

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:51 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 ( 410 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ D )
          & ( r1_xboole_0 @ B @ D )
          & ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( sk_D != sk_D )
    | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['2','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.akmT4puoWe
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 1317 iterations in 0.730s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(sk_D_type, type, sk_D: $i).
% 1.00/1.18  thf(t114_xboole_1, conjecture,
% 1.00/1.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.18     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 1.00/1.18         ( r1_xboole_0 @ C @ D ) ) =>
% 1.00/1.18       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.18        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 1.00/1.18            ( r1_xboole_0 @ C @ D ) ) =>
% 1.00/1.18          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 1.00/1.18  thf('0', plain,
% 1.00/1.18      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 1.00/1.18          sk_D)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(commutativity_k2_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.00/1.18  thf('2', plain,
% 1.00/1.18      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ 
% 1.00/1.18          sk_D)),
% 1.00/1.18      inference('demod', [status(thm)], ['0', '1'])).
% 1.00/1.18  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(symmetry_r1_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.18  thf('5', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.00/1.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.00/1.18  thf(t83_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X7 : $i, X8 : $i]:
% 1.00/1.18         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 1.00/1.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.18  thf('7', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.00/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.18  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.18  thf('10', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 1.00/1.18      inference('sup-', [status(thm)], ['8', '9'])).
% 1.00/1.18  thf('11', plain,
% 1.00/1.18      (![X7 : $i, X8 : $i]:
% 1.00/1.18         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 1.00/1.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.18  thf('12', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 1.00/1.18      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.18  thf(t41_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.00/1.18       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 1.00/1.18           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ sk_D @ X0)
% 1.00/1.18           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('15', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.18  thf('17', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X7 : $i, X8 : $i]:
% 1.00/1.18         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 1.00/1.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.18  thf('19', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('20', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 1.00/1.18           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ sk_D @ X0)
% 1.00/1.18           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['19', '20'])).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (![X7 : $i, X9 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 1.00/1.18          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['21', '22'])).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 1.00/1.18          | (r1_xboole_0 @ sk_D @ 
% 1.00/1.18             (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['14', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      ((((sk_D) != (sk_D))
% 1.00/1.18        | (r1_xboole_0 @ sk_D @ 
% 1.00/1.18           (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['7', '24'])).
% 1.00/1.18  thf('26', plain,
% 1.00/1.18      ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['25'])).
% 1.00/1.18  thf('27', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      ((r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ sk_D)),
% 1.00/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 1.00/1.18  thf('29', plain, ($false), inference('demod', [status(thm)], ['2', '28'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
