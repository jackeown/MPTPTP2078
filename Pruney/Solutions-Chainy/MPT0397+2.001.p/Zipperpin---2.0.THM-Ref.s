%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3RH7aMVkDm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:55 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  316 ( 464 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_setfam_1_type,type,(
    r2_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(t19_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_setfam_1 @ B @ A )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_setfam_1 @ B @ A )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 )
      | ( r1_tarski @ X11 @ ( k1_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d3_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ B )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ A )
                  & ( r1_tarski @ D @ C ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ ( sk_D @ X3 @ X4 ) @ X3 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_setfam_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_setfam_1 @ X2 @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 )
      | ( r1_tarski @ X11 @ ( k1_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('9',plain,(
    r2_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_setfam_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( sk_C_1 @ X11 @ X10 ) )
      | ( r1_tarski @ X11 @ ( k1_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3RH7aMVkDm
% 0.15/0.36  % Computer   : n021.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:06:49 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 104 iterations in 0.145s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r2_setfam_1_type, type, r2_setfam_1: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.43/0.62  thf(t19_setfam_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_setfam_1 @ B @ A ) =>
% 0.43/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( r2_setfam_1 @ B @ A ) =>
% 0.43/0.62          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t19_setfam_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain, ((r2_setfam_1 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t6_setfam_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.43/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((X10) = (k1_xboole_0))
% 0.43/0.62          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 0.43/0.62          | (r1_tarski @ X11 @ (k1_setfam_1 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.43/0.62  thf(d3_setfam_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_setfam_1 @ A @ B ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ~( ( r2_hidden @ C @ B ) & 
% 0.43/0.62              ( ![D:$i]: ( ~( ( r2_hidden @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((r1_tarski @ (sk_D @ X3 @ X4) @ X3)
% 0.43/0.62          | ~ (r2_hidden @ X3 @ X5)
% 0.43/0.62          | ~ (r2_setfam_1 @ X4 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_setfam_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.43/0.62          | ((X0) = (k1_xboole_0))
% 0.43/0.62          | ~ (r2_setfam_1 @ X2 @ X0)
% 0.43/0.62          | (r1_tarski @ (sk_D @ (sk_C_1 @ X1 @ X0) @ X2) @ (sk_C_1 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.43/0.62           (sk_C_1 @ X0 @ sk_A))
% 0.43/0.62          | ((sk_A) = (k1_xboole_0))
% 0.43/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '4'])).
% 0.43/0.62  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.43/0.62           (sk_C_1 @ X0 @ sk_A))
% 0.43/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((X10) = (k1_xboole_0))
% 0.43/0.62          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 0.43/0.62          | (r1_tarski @ X11 @ (k1_setfam_1 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.43/0.62  thf('9', plain, ((r2_setfam_1 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_D @ X3 @ X4) @ X4)
% 0.43/0.62          | ~ (r2_hidden @ X3 @ X5)
% 0.43/0.62          | ~ (r2_setfam_1 @ X4 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_setfam_1])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.43/0.62          | ((sk_A) = (k1_xboole_0))
% 0.43/0.62          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '11'])).
% 0.43/0.62  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.43/0.62          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf(t4_setfam_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_setfam_1 @ X8) @ X9) | ~ (r2_hidden @ X9 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.43/0.62          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ 
% 0.43/0.62             (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf(t1_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.43/0.62       ( r1_tarski @ A @ C ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X0 @ X1)
% 0.43/0.62          | ~ (r1_tarski @ X1 @ X2)
% 0.43/0.62          | (r1_tarski @ X0 @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.43/0.62          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X1)
% 0.43/0.62          | ~ (r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.43/0.62          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C_1 @ X0 @ sk_A))
% 0.43/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C_1 @ X0 @ sk_A))
% 0.43/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['19'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((X10) = (k1_xboole_0))
% 0.43/0.62          | ~ (r1_tarski @ X11 @ (sk_C_1 @ X11 @ X10))
% 0.43/0.62          | (r1_tarski @ X11 @ (k1_setfam_1 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.43/0.62        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.43/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      ((((sk_A) = (k1_xboole_0))
% 0.43/0.62        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.62  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('25', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.43/0.62  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
