%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sswfEVYiZx

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 ( 494 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','10'])).

thf('12',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('25',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['12','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sswfEVYiZx
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:46:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 43 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(t127_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.49          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.20/0.49          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_C @ sk_D)) <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['1'])).
% 0.20/0.49  thf(d7_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t123_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.20/0.49       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((k2_zfmisc_1 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X9))
% 0.20/0.49           = (k3_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49            != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.20/0.49             != (k1_xboole_0))
% 0.20/0.49           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ 
% 0.20/0.49              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ 
% 0.20/0.49              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['1'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49            != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49             != (k1_xboole_0))
% 0.20/0.49           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.20/0.49              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.20/0.49              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.20/0.49          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_C @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['1'])).
% 0.20/0.49  thf('25', plain, (((r1_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['12', '25'])).
% 0.20/0.49  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
