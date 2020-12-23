%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4UfnhBzUrC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  69 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 605 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D )
          & ( r1_xboole_0 @ B @ D ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t64_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
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
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    r1_tarski @ sk_C_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( r1_xboole_0 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( r1_xboole_0 @ sk_C_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('28',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4UfnhBzUrC
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 40 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(t64_xboole_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.46         ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.46       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.46            ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.46          ( r1_xboole_0 @ A @ C ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t64_xboole_1])).
% 0.21/0.46  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t3_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.46            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.46          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.46          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.46          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.46          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.46          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.46  thf('8', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.46  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d3_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.46          | (r2_hidden @ X0 @ X2)
% 0.21/0.46          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.46          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ sk_A @ X0)
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ sk_B)
% 0.21/0.46          | (r1_xboole_0 @ sk_A @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ sk_A @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.46  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.46  thf('19', plain, ((r1_tarski @ sk_C_2 @ sk_D)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.46          | (r2_hidden @ X0 @ X2)
% 0.21/0.46          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.21/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ sk_C_2 @ X0)
% 0.21/0.46          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_D))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.46          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ sk_C_2 @ X0)
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ sk_D)
% 0.21/0.46          | (r1_xboole_0 @ sk_C_2 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_D) | (r1_xboole_0 @ sk_C_2 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.46  thf('26', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.46  thf('28', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.21/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.46  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
