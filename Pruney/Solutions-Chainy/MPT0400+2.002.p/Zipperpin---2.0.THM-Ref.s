%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8fE7KED5N1

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  359 ( 575 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t23_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_setfam_1 @ A @ B )
        & ( r1_setfam_1 @ B @ C ) )
     => ( r1_setfam_1 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_setfam_1 @ A @ B )
          & ( r1_setfam_1 @ B @ C ) )
       => ( r1_setfam_1 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t23_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_setfam_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_setfam_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( sk_D @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r1_setfam_1 @ sk_B @ X1 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( sk_D @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( ( k2_xboole_0 @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) )
        = ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 )
      | ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r1_tarski @ ( sk_C @ X8 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_C_1 )
    | ( r1_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    r1_setfam_1 @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8fE7KED5N1
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 32 iterations in 0.013s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.43  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.43  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.43  thf(t23_setfam_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.20/0.43       ( r1_setfam_1 @ A @ C ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.43        ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.20/0.43          ( r1_setfam_1 @ A @ C ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t23_setfam_1])).
% 0.20/0.43  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_C_1)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(d2_setfam_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.43       ( ![C:$i]:
% 0.20/0.43         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.43              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X7 : $i, X8 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('2', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_D @ X5 @ X6) @ X6)
% 0.20/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.20/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.43  thf('6', plain, ((r1_setfam_1 @ sk_B @ sk_C_1)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_D @ X5 @ X6) @ X6)
% 0.20/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.20/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.43          | (r2_hidden @ (sk_D @ X0 @ sk_C_1) @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | (r2_hidden @ 
% 0.20/0.43             (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1) @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.43  thf('10', plain, ((r1_setfam_1 @ sk_B @ sk_C_1)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((r1_tarski @ X5 @ (sk_D @ X5 @ X6))
% 0.20/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.20/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | ~ (r1_setfam_1 @ sk_B @ X1)
% 0.20/0.43          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ 
% 0.20/0.43             (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ X1)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ 
% 0.20/0.43           (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.43  thf('15', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X7 : $i, X8 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((r1_tarski @ X5 @ (sk_D @ X5 @ X6))
% 0.20/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.20/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('18', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.43          | ~ (r1_setfam_1 @ X0 @ X2)
% 0.20/0.43          | (r1_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ (sk_C @ X1 @ X0) @ X2)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.43  thf('19', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B))
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.43  thf(t12_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.43  thf('20', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i]:
% 0.20/0.43         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.43  thf('21', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | ((k2_xboole_0 @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.43              (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B))
% 0.20/0.43              = (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.43  thf(t11_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.43  thf('22', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.43  thf('23', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ X1)
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.43  thf('24', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | (r1_tarski @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.43             (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['14', '23'])).
% 0.20/0.43  thf('25', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.43           (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.43  thf('26', plain,
% 0.20/0.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ X7 @ X8)
% 0.20/0.43          | ~ (r2_hidden @ X9 @ X8)
% 0.20/0.43          | ~ (r1_tarski @ (sk_C @ X8 @ X7) @ X9))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('27', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_setfam_1 @ sk_A @ X0)
% 0.20/0.43          | ~ (r2_hidden @ 
% 0.20/0.43               (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1) @ X0)
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.43  thf('28', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r2_hidden @ 
% 0.20/0.43             (sk_D @ (sk_D @ (sk_C @ X0 @ sk_A) @ sk_B) @ sk_C_1) @ X0)
% 0.20/0.43          | (r1_setfam_1 @ sk_A @ X0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.43  thf('29', plain,
% 0.20/0.43      (((r1_setfam_1 @ sk_A @ sk_C_1) | (r1_setfam_1 @ sk_A @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.43  thf('30', plain, ((r1_setfam_1 @ sk_A @ sk_C_1)),
% 0.20/0.43      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.43  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
