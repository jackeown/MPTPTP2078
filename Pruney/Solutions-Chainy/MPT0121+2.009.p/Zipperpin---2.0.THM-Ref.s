%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RVaBIUolF4

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:52 EST 2020

% Result     : Theorem 8.15s
% Output     : Refutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  311 ( 775 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_D @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('13',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('18',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != X2 )
      | ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
       != X2 )
      | ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ X1 ) @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_D @ X0 )
       != sk_D )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ( sk_D != sk_D )
    | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('31',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RVaBIUolF4
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.15/8.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.15/8.38  % Solved by: fo/fo7.sh
% 8.15/8.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.15/8.38  % done 989 iterations in 7.930s
% 8.15/8.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.15/8.38  % SZS output start Refutation
% 8.15/8.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.15/8.38  thf(sk_B_type, type, sk_B: $i).
% 8.15/8.38  thf(sk_A_type, type, sk_A: $i).
% 8.15/8.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.15/8.38  thf(sk_D_type, type, sk_D: $i).
% 8.15/8.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.15/8.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.15/8.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.15/8.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.15/8.38  thf(t114_xboole_1, conjecture,
% 8.15/8.38    (![A:$i,B:$i,C:$i,D:$i]:
% 8.15/8.38     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 8.15/8.38         ( r1_xboole_0 @ C @ D ) ) =>
% 8.15/8.38       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 8.15/8.38  thf(zf_stmt_0, negated_conjecture,
% 8.15/8.38    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 8.15/8.38        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 8.15/8.38            ( r1_xboole_0 @ C @ D ) ) =>
% 8.15/8.38          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 8.15/8.38    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 8.15/8.38  thf('0', plain,
% 8.15/8.38      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C_1) @ 
% 8.15/8.38          sk_D)),
% 8.15/8.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.15/8.38  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 8.15/8.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.15/8.38  thf(t3_xboole_0, axiom,
% 8.15/8.38    (![A:$i,B:$i]:
% 8.15/8.38     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 8.15/8.38            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.15/8.38       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.15/8.38            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 8.15/8.38  thf('2', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 8.15/8.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.15/8.38  thf('3', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 8.15/8.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.15/8.38  thf('4', plain,
% 8.15/8.38      (![X0 : $i, X2 : $i, X3 : $i]:
% 8.15/8.38         (~ (r2_hidden @ X2 @ X0)
% 8.15/8.38          | ~ (r2_hidden @ X2 @ X3)
% 8.15/8.38          | ~ (r1_xboole_0 @ X0 @ X3))),
% 8.15/8.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.15/8.38  thf('5', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.15/8.38         ((r1_xboole_0 @ X1 @ X0)
% 8.15/8.38          | ~ (r1_xboole_0 @ X0 @ X2)
% 8.15/8.38          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 8.15/8.38      inference('sup-', [status(thm)], ['3', '4'])).
% 8.15/8.38  thf('6', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         ((r1_xboole_0 @ X0 @ X1)
% 8.15/8.38          | ~ (r1_xboole_0 @ X1 @ X0)
% 8.15/8.38          | (r1_xboole_0 @ X0 @ X1))),
% 8.15/8.38      inference('sup-', [status(thm)], ['2', '5'])).
% 8.15/8.38  thf('7', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.15/8.38      inference('simplify', [status(thm)], ['6'])).
% 8.15/8.38  thf('8', plain, ((r1_xboole_0 @ sk_D @ sk_C_1)),
% 8.15/8.38      inference('sup-', [status(thm)], ['1', '7'])).
% 8.15/8.38  thf(t83_xboole_1, axiom,
% 8.15/8.38    (![A:$i,B:$i]:
% 8.15/8.38     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.15/8.38  thf('9', plain,
% 8.15/8.38      (![X7 : $i, X8 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 8.15/8.38      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.15/8.38  thf('10', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_D))),
% 8.15/8.38      inference('sup-', [status(thm)], ['8', '9'])).
% 8.15/8.38  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 8.15/8.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.15/8.38  thf('12', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.15/8.38      inference('simplify', [status(thm)], ['6'])).
% 8.15/8.38  thf('13', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 8.15/8.38      inference('sup-', [status(thm)], ['11', '12'])).
% 8.15/8.38  thf('14', plain,
% 8.15/8.38      (![X7 : $i, X8 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 8.15/8.38      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.15/8.38  thf('15', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 8.15/8.38      inference('sup-', [status(thm)], ['13', '14'])).
% 8.15/8.38  thf('16', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 8.15/8.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.15/8.38  thf('17', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.15/8.38      inference('simplify', [status(thm)], ['6'])).
% 8.15/8.38  thf('18', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 8.15/8.38      inference('sup-', [status(thm)], ['16', '17'])).
% 8.15/8.38  thf('19', plain,
% 8.15/8.38      (![X7 : $i, X8 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 8.15/8.38      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.15/8.38  thf('20', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 8.15/8.38      inference('sup-', [status(thm)], ['18', '19'])).
% 8.15/8.38  thf(t41_xboole_1, axiom,
% 8.15/8.38    (![A:$i,B:$i,C:$i]:
% 8.15/8.38     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 8.15/8.38       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.15/8.38  thf('21', plain,
% 8.15/8.38      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.15/8.38         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 8.15/8.38           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 8.15/8.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 8.15/8.38  thf('22', plain,
% 8.15/8.38      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.15/8.38         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 8.15/8.38           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 8.15/8.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 8.15/8.38  thf('23', plain,
% 8.15/8.38      (![X7 : $i, X9 : $i]:
% 8.15/8.38         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 8.15/8.38      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.15/8.38  thf('24', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (X2))
% 8.15/8.38          | (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.15/8.38      inference('sup-', [status(thm)], ['22', '23'])).
% 8.15/8.38  thf('25', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 8.15/8.38            != (X2))
% 8.15/8.38          | (r1_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)))),
% 8.15/8.38      inference('sup-', [status(thm)], ['21', '24'])).
% 8.15/8.38  thf('26', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ X1) @ X0) != (sk_D))
% 8.15/8.38          | (r1_xboole_0 @ sk_D @ 
% 8.15/8.38             (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ X1) @ X0)))),
% 8.15/8.38      inference('sup-', [status(thm)], ['20', '25'])).
% 8.15/8.38  thf('27', plain,
% 8.15/8.38      (![X0 : $i]:
% 8.15/8.38         (((k4_xboole_0 @ sk_D @ X0) != (sk_D))
% 8.15/8.38          | (r1_xboole_0 @ sk_D @ 
% 8.15/8.38             (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 8.15/8.38      inference('sup-', [status(thm)], ['15', '26'])).
% 8.15/8.38  thf('28', plain,
% 8.15/8.38      ((((sk_D) != (sk_D))
% 8.15/8.38        | (r1_xboole_0 @ sk_D @ 
% 8.15/8.38           (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C_1)))),
% 8.15/8.38      inference('sup-', [status(thm)], ['10', '27'])).
% 8.15/8.38  thf('29', plain,
% 8.15/8.38      ((r1_xboole_0 @ sk_D @ 
% 8.15/8.38        (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C_1))),
% 8.15/8.38      inference('simplify', [status(thm)], ['28'])).
% 8.15/8.38  thf('30', plain,
% 8.15/8.38      (![X0 : $i, X1 : $i]:
% 8.15/8.38         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.15/8.38      inference('simplify', [status(thm)], ['6'])).
% 8.15/8.38  thf('31', plain,
% 8.15/8.38      ((r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C_1) @ 
% 8.15/8.38        sk_D)),
% 8.15/8.38      inference('sup-', [status(thm)], ['29', '30'])).
% 8.15/8.38  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 8.15/8.38  
% 8.15/8.38  % SZS output end Refutation
% 8.15/8.38  
% 8.15/8.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
