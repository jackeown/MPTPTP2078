%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZdWn3cmHkx

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  405 ( 912 expanded)
%              Number of equality atoms :   49 ( 109 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X41 @ X40 ) @ X40 )
      | ( r1_tarski @ X41 @ ( k1_setfam_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X41 @ ( sk_C_1 @ X41 @ X40 ) )
      | ( r1_tarski @ X41 @ ( k1_setfam_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('19',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X37 ) )
      | ( X36 != X37 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('23',plain,(
    ! [X37: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['30'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZdWn3cmHkx
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 157 iterations in 0.070s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.34/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(t6_setfam_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.34/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (![X40 : $i, X41 : $i]:
% 0.34/0.52         (((X40) = (k1_xboole_0))
% 0.34/0.52          | (r2_hidden @ (sk_C_1 @ X41 @ X40) @ X40)
% 0.34/0.52          | (r1_tarski @ X41 @ (k1_setfam_1 @ X40)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.34/0.52  thf(d1_tarski, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.34/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X28 @ X27)
% 0.34/0.52          | ((X28) = (X25))
% 0.34/0.52          | ((X27) != (k1_tarski @ X25)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X25 : $i, X28 : $i]:
% 0.34/0.52         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.52          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '2'])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         (((X26) != (X25))
% 0.34/0.52          | (r2_hidden @ X26 @ X27)
% 0.34/0.52          | ((X27) != (k1_tarski @ X25)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.52  thf('5', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.34/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.34/0.52  thf(t4_setfam_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X38 : $i, X39 : $i]:
% 0.34/0.52         ((r1_tarski @ (k1_setfam_1 @ X38) @ X39) | ~ (r2_hidden @ X39 @ X38))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X6 : $i, X8 : $i]:
% 0.34/0.52         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((sk_C_1 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.52          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X40 : $i, X41 : $i]:
% 0.34/0.52         (((X40) = (k1_xboole_0))
% 0.34/0.52          | ~ (r1_tarski @ X41 @ (sk_C_1 @ X41 @ X40))
% 0.34/0.52          | (r1_tarski @ X41 @ (k1_setfam_1 @ X40)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X0 @ X0)
% 0.34/0.52          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.52          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('14', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.34/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.52          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['12', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.52          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.34/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.34/0.52  thf(t11_setfam_1, conjecture,
% 0.34/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.34/0.52  thf('19', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.34/0.52  thf('21', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.34/0.52  thf(t16_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.34/0.52          ( ( A ) = ( B ) ) ) ))).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (![X36 : $i, X37 : $i]:
% 0.34/0.52         (~ (r1_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X37))
% 0.34/0.52          | ((X36) != (X37)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X37 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))),
% 0.34/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.34/0.52  thf('24', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.34/0.52      inference('sup-', [status(thm)], ['21', '23'])).
% 0.34/0.52  thf('25', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.34/0.52  thf(d5_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.34/0.52       ( ![D:$i]:
% 0.34/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.34/0.52         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.34/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.34/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.52  thf(t3_boole, axiom,
% 0.34/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.52  thf('27', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.34/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.34/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.34/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['27', '29'])).
% 0.34/0.52  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.34/0.52          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['26', '31'])).
% 0.34/0.52  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.52  thf(t83_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (![X10 : $i, X12 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.52  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.52  thf('38', plain, ($false),
% 0.34/0.52      inference('demod', [status(thm)], ['24', '25', '37'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
