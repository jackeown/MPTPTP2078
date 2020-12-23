%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sI501MkBy3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  392 ( 863 expanded)
%              Number of equality atoms :   34 (  67 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t3_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t3_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X12
       != ( k1_setfam_1 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X12 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r2_hidden @ X16 @ ( k1_setfam_1 @ X13 ) )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X15 @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( sk_B @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_B @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i,X18: $i] :
      ( ( X18
       != ( k1_setfam_1 @ X13 ) )
      | ( X18 = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('27',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('29',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25','27','28','29','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sI501MkBy3
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 58 iterations in 0.083s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.54  thf(t3_setfam_1, conjecture,
% 0.20/0.54    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t3_setfam_1])).
% 0.20/0.54  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_A) @ (k3_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t7_xboole_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.54  thf(d3_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf(d1_setfam_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.54       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (((X12) != (k1_setfam_1 @ X13))
% 0.20/0.54          | ~ (r2_hidden @ X15 @ X13)
% 0.20/0.54          | (r2_hidden @ X16 @ X15)
% 0.20/0.54          | ~ (r2_hidden @ X16 @ X12)
% 0.20/0.54          | ((X13) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (((X13) = (k1_xboole_0))
% 0.20/0.54          | ~ (r2_hidden @ X16 @ (k1_setfam_1 @ X13))
% 0.20/0.54          | (r2_hidden @ X16 @ X15)
% 0.20/0.54          | ~ (r2_hidden @ X15 @ X13))),
% 0.20/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.20/0.54          | ~ (r2_hidden @ X2 @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ (sk_B @ X0))
% 0.20/0.54          | (r1_tarski @ (k1_setfam_1 @ X0) @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ (sk_B @ X0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf(d4_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.54          | ~ (r2_hidden @ X7 @ X5)
% 0.20/0.54          | (r2_hidden @ X7 @ X8)
% 0.20/0.54          | ((X8) != (k3_tarski @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 0.20/0.54          | ~ (r2_hidden @ X7 @ X5)
% 0.20/0.54          | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r1_tarski @ X0 @ X1)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ (sk_B @ X0)) @ (k3_tarski @ X0))
% 0.20/0.54          | (r1_tarski @ (sk_B @ X0) @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0))
% 0.20/0.54          | ((X0) = (k1_xboole_0))
% 0.20/0.54          | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0)) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ X1 @ (k3_tarski @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (sk_B @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | (r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ (k3_tarski @ X0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ (k3_tarski @ X0))
% 0.20/0.54          | (r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | (r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0))
% 0.20/0.54          | (r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('24', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_A) @ (k3_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X13 : $i, X18 : $i]:
% 0.20/0.54         (((X18) != (k1_setfam_1 @ X13))
% 0.20/0.54          | ((X18) = (k1_xboole_0))
% 0.20/0.54          | ((X13) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.54  thf('27', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.54  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.54  thf('29', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.54  thf('34', plain, ($false),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '25', '27', '28', '29', '33'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
