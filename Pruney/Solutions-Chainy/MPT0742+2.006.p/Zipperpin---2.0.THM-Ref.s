%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xzGQXoPRQY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 352 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  467 (3023 expanded)
%              Number of equality atoms :   17 ( 116 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ( X11 = X10 )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t31_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( v3_ordinal1 @ B )
            & ( r1_tarski @ B @ A ) ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_ordinal1])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_ordinal1])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','15'])).

thf(t32_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ~ ( ( r1_tarski @ A @ B )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ~ ( ( r2_hidden @ C @ A )
                  & ! [D: $i] :
                      ( ( v3_ordinal1 @ D )
                     => ( ( r2_hidden @ D @ A )
                       => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ~ ( ( r1_tarski @ A @ B )
            & ( A != k1_xboole_0 )
            & ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ~ ( ( r2_hidden @ C @ A )
                    & ! [D: $i] :
                        ( ( v3_ordinal1 @ D )
                       => ( ( r2_hidden @ D @ A )
                         => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_ordinal1])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ ( sk_D @ X17 ) @ sk_A )
      | ~ ( r2_hidden @ X17 @ sk_A )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('29',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X17 ) )
      | ~ ( r2_hidden @ X17 @ sk_A )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('46',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X17: $i] :
      ( ~ ( r1_ordinal1 @ X17 @ ( sk_D @ X17 ) )
      | ~ ( r2_hidden @ X17 @ sk_A )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('51',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','31'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('53',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xzGQXoPRQY
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 711 iterations in 0.269s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(sk_D_type, type, sk_D: $i > $i).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.72  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.52/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.72  thf('0', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.72  thf(t24_ordinal1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.52/0.72                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X10)
% 0.52/0.72          | (r2_hidden @ X11 @ X10)
% 0.52/0.72          | ((X11) = (X10))
% 0.52/0.72          | (r2_hidden @ X10 @ X11)
% 0.52/0.72          | ~ (v3_ordinal1 @ X11))),
% 0.52/0.72      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.52/0.72  thf(t7_ordinal1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X1)
% 0.52/0.72          | (r2_hidden @ X0 @ X1)
% 0.52/0.72          | ((X1) = (X0))
% 0.52/0.72          | ~ (v3_ordinal1 @ X0)
% 0.52/0.72          | ~ (r1_tarski @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ k1_xboole_0)
% 0.52/0.72          | ((X0) = (k1_xboole_0))
% 0.52/0.72          | (r2_hidden @ k1_xboole_0 @ X0)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '3'])).
% 0.52/0.72  thf('5', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.72  thf(t31_ordinal1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( ![B:$i]:
% 0.52/0.72         ( ( r2_hidden @ B @ A ) =>
% 0.52/0.72           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.52/0.72       ( v3_ordinal1 @ A ) ))).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X14 : $i]: ((v3_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.52/0.72      inference('cnf', [status(esa)], [t31_ordinal1])).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (![X0 : $i]: ((v3_ordinal1 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('9', plain, ((v3_ordinal1 @ k1_xboole_0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['5', '8'])).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((X0) = (k1_xboole_0))
% 0.52/0.72          | (r2_hidden @ k1_xboole_0 @ X0)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['4', '9'])).
% 0.52/0.72  thf(t7_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ~( ( r2_hidden @ A @ B ) & 
% 0.52/0.72          ( ![C:$i]:
% 0.52/0.72            ( ~( ( r2_hidden @ C @ B ) & 
% 0.52/0.72                 ( ![D:$i]:
% 0.52/0.72                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X5 @ X6) | (r2_hidden @ (sk_C_1 @ X6) @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X0)
% 0.52/0.72          | ((X0) = (k1_xboole_0))
% 0.52/0.72          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X14 : $i]: ((v3_ordinal1 @ X14) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.52/0.72      inference('cnf', [status(esa)], [t31_ordinal1])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X5 @ X6) | (r2_hidden @ (sk_C_1 @ X6) @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (![X0 : $i]: ((v3_ordinal1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X0 : $i]: ((r2_hidden @ (sk_C_1 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('clc', [status(thm)], ['12', '15'])).
% 0.52/0.72  thf(t32_ordinal1, conjecture,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.72            ( ![C:$i]:
% 0.52/0.72              ( ( v3_ordinal1 @ C ) =>
% 0.52/0.72                ( ~( ( r2_hidden @ C @ A ) & 
% 0.52/0.72                     ( ![D:$i]:
% 0.52/0.72                       ( ( v3_ordinal1 @ D ) =>
% 0.52/0.72                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i]:
% 0.52/0.72        ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.72               ( ![C:$i]:
% 0.52/0.72                 ( ( v3_ordinal1 @ C ) =>
% 0.52/0.72                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.52/0.72                        ( ![D:$i]:
% 0.52/0.72                          ( ( v3_ordinal1 @ D ) =>
% 0.52/0.72                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X17 : $i]:
% 0.52/0.72         ((r2_hidden @ (sk_D @ X17) @ sk_A)
% 0.52/0.72          | ~ (r2_hidden @ X17 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X17))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      ((((sk_A) = (k1_xboole_0))
% 0.52/0.72        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.52/0.72        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.72  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.52/0.72        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X0 : $i]: ((r2_hidden @ (sk_C_1 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('clc', [status(thm)], ['12', '15'])).
% 0.52/0.72  thf('22', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(d3_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.72          | (r2_hidden @ X0 @ X2)
% 0.52/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['21', '24'])).
% 0.52/0.72  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_B_1)),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.52/0.72  thf(t23_ordinal1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (![X8 : $i, X9 : $i]:
% 0.52/0.72         ((v3_ordinal1 @ X8) | ~ (v3_ordinal1 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.72  thf('30', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('31', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf('32', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.52/0.72      inference('demod', [status(thm)], ['20', '31'])).
% 0.52/0.72  thf('33', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf(t26_ordinal1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      (![X12 : $i, X13 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X12)
% 0.52/0.72          | (r1_ordinal1 @ X13 @ X12)
% 0.52/0.72          | (r2_hidden @ X12 @ X13)
% 0.52/0.72          | ~ (v3_ordinal1 @ X13))),
% 0.52/0.72      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X5 @ X6)
% 0.52/0.72          | ~ (r2_hidden @ X7 @ X6)
% 0.52/0.72          | ~ (r2_hidden @ X7 @ (sk_C_1 @ X6)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.72      inference('condensation', [status(thm)], ['35'])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.52/0.72          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.52/0.72          | ~ (v3_ordinal1 @ X1)
% 0.52/0.72          | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['34', '36'])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0)
% 0.52/0.72          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['33', '37'])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.52/0.72        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['32', '38'])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      (![X0 : $i]: ((r2_hidden @ (sk_C_1 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('clc', [status(thm)], ['12', '15'])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X17 : $i]:
% 0.52/0.72         ((v3_ordinal1 @ (sk_D @ X17))
% 0.52/0.72          | ~ (r2_hidden @ X17 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X17))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      ((((sk_A) = (k1_xboole_0))
% 0.52/0.72        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.52/0.72        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.72  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('44', plain,
% 0.52/0.72      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.52/0.72        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.52/0.72  thf('45', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf('46', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['44', '45'])).
% 0.52/0.72  thf('47', plain,
% 0.52/0.72      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['39', '46'])).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      (![X17 : $i]:
% 0.52/0.72         (~ (r1_ordinal1 @ X17 @ (sk_D @ X17))
% 0.52/0.72          | ~ (r2_hidden @ X17 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X17))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.52/0.72        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.72  thf('50', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf('51', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.52/0.72      inference('demod', [status(thm)], ['20', '31'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X5 @ X6) | (r2_hidden @ (sk_C_1 @ X6) @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.72  thf('53', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.52/0.72      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.72  thf('54', plain, ($false),
% 0.52/0.72      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
