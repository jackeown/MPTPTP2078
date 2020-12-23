%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zWUnsCHACP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 410 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
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

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['11','21'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zWUnsCHACP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:31 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 44 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(t67_xboole_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.47         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.47       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.47            ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.47          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.21/0.47  thf('0', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('2', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_A @ X0)
% 0.21/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ sk_C_2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.47          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.47          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_A @ X0)
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ sk_C_2)
% 0.21/0.47          | (r1_xboole_0 @ sk_A @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_C_2) | (r1_xboole_0 @ sk_A @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.47          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.47          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ sk_A)
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ sk_B)
% 0.21/0.47          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.47  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '21'])).
% 0.21/0.47  thf(t66_xboole_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.47  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
