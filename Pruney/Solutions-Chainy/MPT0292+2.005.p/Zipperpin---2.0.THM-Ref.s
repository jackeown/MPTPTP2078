%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D01s0IwMUw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:55 EST 2020

% Result     : Theorem 4.94s
% Output     : Refutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 106 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   19
%              Number of atoms          :  508 (1058 expanded)
%              Number of equality atoms :   48 (  96 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X25: $i] :
      ( ( X25
        = ( k3_tarski @ X21 ) )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ ( sk_D_1 @ X25 @ X21 ) )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X21: $i,X25: $i] :
      ( ( X25
        = ( k3_tarski @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X25 @ X21 ) @ X21 )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('8',plain,(
    ! [X21: $i,X25: $i] :
      ( ( X25
        = ( k3_tarski @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X25 @ X21 ) @ X21 )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('9',plain,(
    ! [X21: $i,X25: $i,X26: $i] :
      ( ( X25
        = ( k3_tarski @ X21 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X26 )
      | ~ ( r2_hidden @ X26 @ X21 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
        = ( k3_xboole_0 @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_D_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X21: $i,X25: $i,X26: $i] :
      ( ( X25
        = ( k3_tarski @ X21 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X26 )
      | ~ ( r2_hidden @ X26 @ X21 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D01s0IwMUw
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:26 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.94/5.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.94/5.16  % Solved by: fo/fo7.sh
% 4.94/5.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.94/5.16  % done 831 iterations in 4.704s
% 4.94/5.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.94/5.16  % SZS output start Refutation
% 4.94/5.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.94/5.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.94/5.16  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 4.94/5.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.94/5.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.94/5.16  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.94/5.16  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.94/5.16  thf(sk_A_type, type, sk_A: $i).
% 4.94/5.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.94/5.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.94/5.16  thf(t99_zfmisc_1, conjecture,
% 4.94/5.16    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 4.94/5.16  thf(zf_stmt_0, negated_conjecture,
% 4.94/5.16    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 4.94/5.16    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 4.94/5.16  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 4.94/5.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.94/5.16  thf(d4_tarski, axiom,
% 4.94/5.16    (![A:$i,B:$i]:
% 4.94/5.16     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 4.94/5.16       ( ![C:$i]:
% 4.94/5.16         ( ( r2_hidden @ C @ B ) <=>
% 4.94/5.16           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 4.94/5.16  thf('1', plain,
% 4.94/5.16      (![X21 : $i, X25 : $i]:
% 4.94/5.16         (((X25) = (k3_tarski @ X21))
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X25 @ X21) @ (sk_D_1 @ X25 @ X21))
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X25))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_tarski])).
% 4.94/5.16  thf(d10_xboole_0, axiom,
% 4.94/5.16    (![A:$i,B:$i]:
% 4.94/5.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.94/5.16  thf('2', plain,
% 4.94/5.16      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 4.94/5.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.94/5.16  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 4.94/5.16      inference('simplify', [status(thm)], ['2'])).
% 4.94/5.16  thf(d1_zfmisc_1, axiom,
% 4.94/5.16    (![A:$i,B:$i]:
% 4.94/5.16     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.94/5.16       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.94/5.16  thf('4', plain,
% 4.94/5.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.94/5.16         (~ (r1_tarski @ X15 @ X16)
% 4.94/5.16          | (r2_hidden @ X15 @ X17)
% 4.94/5.16          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 4.94/5.16      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.94/5.16  thf('5', plain,
% 4.94/5.16      (![X15 : $i, X16 : $i]:
% 4.94/5.16         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 4.94/5.16      inference('simplify', [status(thm)], ['4'])).
% 4.94/5.16  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.94/5.16      inference('sup-', [status(thm)], ['3', '5'])).
% 4.94/5.16  thf('7', plain,
% 4.94/5.16      (![X21 : $i, X25 : $i]:
% 4.94/5.16         (((X25) = (k3_tarski @ X21))
% 4.94/5.16          | (r2_hidden @ (sk_D_1 @ X25 @ X21) @ X21)
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X25))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_tarski])).
% 4.94/5.16  thf('8', plain,
% 4.94/5.16      (![X21 : $i, X25 : $i]:
% 4.94/5.16         (((X25) = (k3_tarski @ X21))
% 4.94/5.16          | (r2_hidden @ (sk_D_1 @ X25 @ X21) @ X21)
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X25))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_tarski])).
% 4.94/5.16  thf('9', plain,
% 4.94/5.16      (![X21 : $i, X25 : $i, X26 : $i]:
% 4.94/5.16         (((X25) = (k3_tarski @ X21))
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X26)
% 4.94/5.16          | ~ (r2_hidden @ X26 @ X21)
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X25))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_tarski])).
% 4.94/5.16  thf('10', plain,
% 4.94/5.16      (![X0 : $i, X1 : $i]:
% 4.94/5.16         ((r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1))
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 4.94/5.16          | ~ (r2_hidden @ X0 @ X1)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1)))),
% 4.94/5.16      inference('sup-', [status(thm)], ['8', '9'])).
% 4.94/5.16  thf('11', plain,
% 4.94/5.16      (![X0 : $i, X1 : $i]:
% 4.94/5.16         (~ (r2_hidden @ X0 @ X1)
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1))
% 4.94/5.16          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1))),
% 4.94/5.16      inference('simplify', [status(thm)], ['10'])).
% 4.94/5.16  thf('12', plain,
% 4.94/5.16      (![X0 : $i, X1 : $i]:
% 4.94/5.16         ((r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1))
% 4.94/5.16          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1))
% 4.94/5.16          | ~ (r2_hidden @ X0 @ X1))),
% 4.94/5.16      inference('sup-', [status(thm)], ['7', '11'])).
% 4.94/5.16  thf('13', plain,
% 4.94/5.16      (![X0 : $i, X1 : $i]:
% 4.94/5.16         (~ (r2_hidden @ X0 @ X1)
% 4.94/5.16          | ((X0) = (k3_tarski @ X1))
% 4.94/5.16          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1))),
% 4.94/5.16      inference('simplify', [status(thm)], ['12'])).
% 4.94/5.16  thf('14', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         ((r2_hidden @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ (k1_zfmisc_1 @ X0))
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('sup-', [status(thm)], ['6', '13'])).
% 4.94/5.16  thf('15', plain,
% 4.94/5.16      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.94/5.16         (~ (r2_hidden @ X18 @ X17)
% 4.94/5.16          | (r1_tarski @ X18 @ X16)
% 4.94/5.16          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 4.94/5.16      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.94/5.16  thf('16', plain,
% 4.94/5.16      (![X16 : $i, X18 : $i]:
% 4.94/5.16         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 4.94/5.16      inference('simplify', [status(thm)], ['15'])).
% 4.94/5.16  thf('17', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.94/5.16      inference('sup-', [status(thm)], ['14', '16'])).
% 4.94/5.16  thf(l32_xboole_1, axiom,
% 4.94/5.16    (![A:$i,B:$i]:
% 4.94/5.16     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.94/5.16  thf('18', plain,
% 4.94/5.16      (![X9 : $i, X11 : $i]:
% 4.94/5.16         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 4.94/5.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.94/5.16  thf('19', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | ((k4_xboole_0 @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16              = (k1_xboole_0)))),
% 4.94/5.16      inference('sup-', [status(thm)], ['17', '18'])).
% 4.94/5.16  thf(t48_xboole_1, axiom,
% 4.94/5.16    (![A:$i,B:$i]:
% 4.94/5.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.94/5.16  thf('20', plain,
% 4.94/5.16      (![X13 : $i, X14 : $i]:
% 4.94/5.16         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.94/5.16           = (k3_xboole_0 @ X13 @ X14))),
% 4.94/5.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.94/5.16  thf('21', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((k4_xboole_0 @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ k1_xboole_0)
% 4.94/5.16            = (k3_xboole_0 @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('sup+', [status(thm)], ['19', '20'])).
% 4.94/5.16  thf(t3_boole, axiom,
% 4.94/5.16    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.94/5.16  thf('22', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 4.94/5.16      inference('cnf', [status(esa)], [t3_boole])).
% 4.94/5.16  thf('23', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 4.94/5.16            = (k3_xboole_0 @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('demod', [status(thm)], ['21', '22'])).
% 4.94/5.16  thf(d4_xboole_0, axiom,
% 4.94/5.16    (![A:$i,B:$i,C:$i]:
% 4.94/5.16     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 4.94/5.16       ( ![D:$i]:
% 4.94/5.16         ( ( r2_hidden @ D @ C ) <=>
% 4.94/5.16           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.94/5.16  thf('24', plain,
% 4.94/5.16      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.94/5.16         (~ (r2_hidden @ X4 @ X3)
% 4.94/5.16          | (r2_hidden @ X4 @ X2)
% 4.94/5.16          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.94/5.16  thf('25', plain,
% 4.94/5.16      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.94/5.16         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 4.94/5.16      inference('simplify', [status(thm)], ['24'])).
% 4.94/5.16  thf('26', plain,
% 4.94/5.16      (![X0 : $i, X1 : $i]:
% 4.94/5.16         (~ (r2_hidden @ X1 @ (sk_D_1 @ X0 @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | (r2_hidden @ X1 @ X0))),
% 4.94/5.16      inference('sup-', [status(thm)], ['23', '25'])).
% 4.94/5.16  thf('27', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('sup-', [status(thm)], ['1', '26'])).
% 4.94/5.16  thf('28', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.94/5.16      inference('simplify', [status(thm)], ['27'])).
% 4.94/5.16  thf('29', plain,
% 4.94/5.16      (![X21 : $i, X25 : $i, X26 : $i]:
% 4.94/5.16         (((X25) = (k3_tarski @ X21))
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X26)
% 4.94/5.16          | ~ (r2_hidden @ X26 @ X21)
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X25 @ X21) @ X25))),
% 4.94/5.16      inference('cnf', [status(esa)], [d4_tarski])).
% 4.94/5.16  thf('30', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('sup-', [status(thm)], ['28', '29'])).
% 4.94/5.16  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.94/5.16      inference('sup-', [status(thm)], ['3', '5'])).
% 4.94/5.16  thf('32', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('demod', [status(thm)], ['30', '31'])).
% 4.94/5.16  thf('33', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.94/5.16          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.94/5.16      inference('simplify', [status(thm)], ['32'])).
% 4.94/5.16  thf('34', plain,
% 4.94/5.16      (![X0 : $i]:
% 4.94/5.16         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.94/5.16          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.94/5.16      inference('simplify', [status(thm)], ['27'])).
% 4.94/5.16  thf('35', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 4.94/5.16      inference('clc', [status(thm)], ['33', '34'])).
% 4.94/5.16  thf('36', plain, (((sk_A) != (sk_A))),
% 4.94/5.16      inference('demod', [status(thm)], ['0', '35'])).
% 4.94/5.16  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 4.94/5.16  
% 4.94/5.16  % SZS output end Refutation
% 4.94/5.16  
% 4.94/5.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
