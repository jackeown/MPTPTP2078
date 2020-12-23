%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RIKIVuaYF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:52 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 403 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k4_xboole_0 @ X5 @ X7 )
       != X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != X2 )
      | ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
       != X2 )
      | ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ X1 ) @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ( sk_D != sk_D )
    | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RIKIVuaYF
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:57 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 2.34/2.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.34/2.55  % Solved by: fo/fo7.sh
% 2.34/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.34/2.55  % done 418 iterations in 2.096s
% 2.34/2.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.34/2.55  % SZS output start Refutation
% 2.34/2.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.34/2.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.34/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.34/2.55  thf(sk_D_type, type, sk_D: $i).
% 2.34/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.34/2.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.34/2.55  thf(sk_C_type, type, sk_C: $i).
% 2.34/2.55  thf(t114_xboole_1, conjecture,
% 2.34/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.55     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 2.34/2.55         ( r1_xboole_0 @ C @ D ) ) =>
% 2.34/2.55       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 2.34/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.34/2.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.55        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 2.34/2.55            ( r1_xboole_0 @ C @ D ) ) =>
% 2.34/2.55          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 2.34/2.55    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 2.34/2.55  thf('0', plain,
% 2.34/2.55      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 2.34/2.55          sk_D)),
% 2.34/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.55  thf('1', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 2.34/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.55  thf(symmetry_r1_xboole_0, axiom,
% 2.34/2.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.34/2.55  thf('2', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i]:
% 2.34/2.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.34/2.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.34/2.55  thf('3', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 2.34/2.55      inference('sup-', [status(thm)], ['1', '2'])).
% 2.34/2.55  thf(t83_xboole_1, axiom,
% 2.34/2.55    (![A:$i,B:$i]:
% 2.34/2.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.34/2.55  thf('4', plain,
% 2.34/2.55      (![X5 : $i, X6 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.34/2.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.34/2.55  thf('5', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 2.34/2.55      inference('sup-', [status(thm)], ['3', '4'])).
% 2.34/2.55  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 2.34/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.55  thf('7', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i]:
% 2.34/2.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.34/2.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.34/2.55  thf('8', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 2.34/2.55      inference('sup-', [status(thm)], ['6', '7'])).
% 2.34/2.55  thf('9', plain,
% 2.34/2.55      (![X5 : $i, X6 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.34/2.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.34/2.55  thf('10', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 2.34/2.55      inference('sup-', [status(thm)], ['8', '9'])).
% 2.34/2.55  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 2.34/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.55  thf('12', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i]:
% 2.34/2.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.34/2.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.34/2.55  thf('13', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 2.34/2.55      inference('sup-', [status(thm)], ['11', '12'])).
% 2.34/2.55  thf('14', plain,
% 2.34/2.55      (![X5 : $i, X6 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.34/2.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.34/2.55  thf('15', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 2.34/2.55      inference('sup-', [status(thm)], ['13', '14'])).
% 2.34/2.55  thf(t41_xboole_1, axiom,
% 2.34/2.55    (![A:$i,B:$i,C:$i]:
% 2.34/2.55     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.34/2.55       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.34/2.55  thf('16', plain,
% 2.34/2.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.34/2.55         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 2.34/2.55           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.34/2.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.34/2.55  thf('17', plain,
% 2.34/2.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.34/2.55         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 2.34/2.55           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.34/2.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.34/2.55  thf('18', plain,
% 2.34/2.55      (![X5 : $i, X7 : $i]:
% 2.34/2.55         ((r1_xboole_0 @ X5 @ X7) | ((k4_xboole_0 @ X5 @ X7) != (X5)))),
% 2.34/2.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.34/2.55  thf('19', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (X2))
% 2.34/2.55          | (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.34/2.55      inference('sup-', [status(thm)], ['17', '18'])).
% 2.34/2.55  thf('20', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 2.34/2.55            != (X2))
% 2.34/2.55          | (r1_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)))),
% 2.34/2.55      inference('sup-', [status(thm)], ['16', '19'])).
% 2.34/2.55  thf('21', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ X1) @ X0) != (sk_D))
% 2.34/2.55          | (r1_xboole_0 @ sk_D @ 
% 2.34/2.55             (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ X1) @ X0)))),
% 2.34/2.55      inference('sup-', [status(thm)], ['15', '20'])).
% 2.34/2.55  thf('22', plain,
% 2.34/2.55      (![X0 : $i]:
% 2.34/2.55         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 2.34/2.55          | (r1_xboole_0 @ sk_D @ 
% 2.34/2.55             (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 2.34/2.55      inference('sup-', [status(thm)], ['10', '21'])).
% 2.34/2.55  thf('23', plain,
% 2.34/2.55      ((((sk_D) != (sk_D))
% 2.34/2.55        | (r1_xboole_0 @ sk_D @ 
% 2.34/2.55           (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C)))),
% 2.34/2.55      inference('sup-', [status(thm)], ['5', '22'])).
% 2.34/2.55  thf('24', plain,
% 2.34/2.55      ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.34/2.55      inference('simplify', [status(thm)], ['23'])).
% 2.34/2.55  thf('25', plain,
% 2.34/2.55      (![X0 : $i, X1 : $i]:
% 2.34/2.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.34/2.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.34/2.55  thf('26', plain,
% 2.34/2.55      ((r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ sk_D)),
% 2.34/2.55      inference('sup-', [status(thm)], ['24', '25'])).
% 2.34/2.55  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 2.34/2.55  
% 2.34/2.55  % SZS output end Refutation
% 2.34/2.55  
% 2.34/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
