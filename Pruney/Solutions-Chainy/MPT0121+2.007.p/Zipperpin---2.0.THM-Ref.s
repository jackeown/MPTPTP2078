%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tvXhZzBpYR

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:52 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  371 ( 596 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( sk_D != sk_D )
    | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['2','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tvXhZzBpYR
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.58/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.78  % Solved by: fo/fo7.sh
% 1.58/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.78  % done 1425 iterations in 1.331s
% 1.58/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.78  % SZS output start Refutation
% 1.58/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.58/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.58/1.78  thf(sk_D_type, type, sk_D: $i).
% 1.58/1.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.58/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(t114_xboole_1, conjecture,
% 1.58/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.58/1.78     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 1.58/1.78         ( r1_xboole_0 @ C @ D ) ) =>
% 1.58/1.78       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 1.58/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.58/1.78        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 1.58/1.78            ( r1_xboole_0 @ C @ D ) ) =>
% 1.58/1.78          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 1.58/1.78    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 1.58/1.78  thf('0', plain,
% 1.58/1.78      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 1.58/1.78          sk_D)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(t4_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.58/1.78       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.58/1.78  thf('1', plain,
% 1.58/1.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.58/1.78         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 1.58/1.78           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.58/1.78  thf('2', plain,
% 1.58/1.78      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 1.58/1.78          sk_D)),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(symmetry_r1_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.58/1.78  thf('4', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('5', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 1.58/1.78      inference('sup-', [status(thm)], ['3', '4'])).
% 1.58/1.78  thf(t83_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.58/1.78  thf('6', plain,
% 1.58/1.78      (![X12 : $i, X13 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.58/1.78      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.58/1.78  thf('7', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 1.58/1.78      inference('sup-', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('9', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('10', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.58/1.78      inference('sup-', [status(thm)], ['8', '9'])).
% 1.58/1.78  thf('11', plain,
% 1.58/1.78      (![X12 : $i, X13 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.58/1.78      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.58/1.78  thf('12', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.58/1.78      inference('sup-', [status(thm)], ['10', '11'])).
% 1.58/1.78  thf(t53_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.58/1.78       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.58/1.78  thf('13', plain,
% 1.58/1.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.58/1.78           = (k3_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ (k4_xboole_0 @ X9 @ X11)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t53_xboole_1])).
% 1.58/1.78  thf('14', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0))
% 1.58/1.78           = (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['12', '13'])).
% 1.58/1.78  thf(t48_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.58/1.78  thf('15', plain,
% 1.58/1.78      (![X4 : $i, X5 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 1.58/1.78           = (k3_xboole_0 @ X4 @ X5))),
% 1.58/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.58/1.78  thf('16', plain,
% 1.58/1.78      (![X4 : $i, X5 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 1.58/1.78           = (k3_xboole_0 @ X4 @ X5))),
% 1.58/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.58/1.78  thf('17', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.58/1.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['15', '16'])).
% 1.58/1.78  thf(t47_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.58/1.78  thf('18', plain,
% 1.58/1.78      (![X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3))
% 1.58/1.78           = (k4_xboole_0 @ X2 @ X3))),
% 1.58/1.78      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.58/1.78  thf('19', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X1 @ X0)
% 1.58/1.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['17', '18'])).
% 1.58/1.78  thf('20', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0))
% 1.58/1.78           = (k4_xboole_0 @ sk_D @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['14', '19'])).
% 1.58/1.78  thf('21', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('22', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('23', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 1.58/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.58/1.78  thf('24', plain,
% 1.58/1.78      (![X12 : $i, X13 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.58/1.78      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.58/1.78  thf('25', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 1.58/1.78      inference('sup-', [status(thm)], ['23', '24'])).
% 1.58/1.78  thf('26', plain,
% 1.58/1.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.58/1.78           = (k3_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ (k4_xboole_0 @ X9 @ X11)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t53_xboole_1])).
% 1.58/1.78  thf('27', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0))
% 1.58/1.78           = (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['25', '26'])).
% 1.58/1.78  thf('28', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X1 @ X0)
% 1.58/1.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['17', '18'])).
% 1.58/1.78  thf('29', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0))
% 1.58/1.78           = (k4_xboole_0 @ sk_D @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['27', '28'])).
% 1.58/1.78  thf('30', plain,
% 1.58/1.78      (![X12 : $i, X14 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.58/1.78  thf('31', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 1.58/1.78          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['29', '30'])).
% 1.58/1.78  thf('32', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 1.58/1.78          | (r1_xboole_0 @ sk_D @ 
% 1.58/1.78             (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['20', '31'])).
% 1.58/1.78  thf('33', plain,
% 1.58/1.78      ((((sk_D) != (sk_D))
% 1.58/1.78        | (r1_xboole_0 @ sk_D @ 
% 1.58/1.78           (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['7', '32'])).
% 1.58/1.78  thf('34', plain,
% 1.58/1.78      ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['33'])).
% 1.58/1.78  thf('35', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('36', plain,
% 1.58/1.78      ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ sk_D)),
% 1.58/1.78      inference('sup-', [status(thm)], ['34', '35'])).
% 1.58/1.78  thf('37', plain, ($false), inference('demod', [status(thm)], ['2', '36'])).
% 1.58/1.78  
% 1.58/1.78  % SZS output end Refutation
% 1.58/1.78  
% 1.58/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
