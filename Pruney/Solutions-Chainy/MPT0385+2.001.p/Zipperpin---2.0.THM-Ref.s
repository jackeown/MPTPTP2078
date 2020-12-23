%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w9jwfsAGek

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:32 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 101 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  426 ( 955 expanded)
%              Number of equality atoms :   29 (  55 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X13
       != ( k1_setfam_1 @ X14 ) )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X17 @ X13 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ ( k1_setfam_1 @ X14 ) )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X16 @ X14 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_setfam_1 @ X0 ) ) @ ( sk_C @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X14: $i,X19: $i] :
      ( ( X19
       != ( k1_setfam_1 @ X14 ) )
      | ( X19 = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('29',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('31',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27','29','30','31','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w9jwfsAGek
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 66 iterations in 0.087s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.56  thf(t3_setfam_1, conjecture,
% 0.37/0.56    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t3_setfam_1])).
% 0.37/0.56  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_A) @ (k3_tarski @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf(d1_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.37/0.56         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.56       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.56         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.56               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.37/0.56         (((X13) != (k1_setfam_1 @ X14))
% 0.37/0.56          | ~ (r2_hidden @ X16 @ X14)
% 0.37/0.56          | (r2_hidden @ X17 @ X16)
% 0.37/0.56          | ~ (r2_hidden @ X17 @ X13)
% 0.37/0.56          | ((X14) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.37/0.56         (((X14) = (k1_xboole_0))
% 0.37/0.56          | ~ (r2_hidden @ X17 @ (k1_setfam_1 @ X14))
% 0.37/0.56          | (r2_hidden @ X17 @ X16)
% 0.37/0.56          | ~ (r2_hidden @ X16 @ X14))),
% 0.37/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.37/0.56          | ~ (r2_hidden @ X2 @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.37/0.56          | ((X0) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | ((X0) = (k1_xboole_0))
% 0.37/0.56          | (r2_hidden @ (sk_C @ X2 @ (k1_setfam_1 @ X0)) @ (sk_C @ X1 @ X0))
% 0.37/0.56          | (r1_tarski @ (k1_setfam_1 @ X0) @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '5'])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf(d4_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.37/0.56       ( ![C:$i]:
% 0.37/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.56           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X4 @ X5)
% 0.37/0.56          | ~ (r2_hidden @ X6 @ X4)
% 0.37/0.56          | (r2_hidden @ X6 @ X7)
% 0.37/0.56          | ((X7) != (k3_tarski @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_tarski])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.37/0.56          | ~ (r2_hidden @ X6 @ X4)
% 0.37/0.56          | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ X2)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X2 @ (sk_C @ X1 @ X0)) @ (k3_tarski @ X0))
% 0.37/0.56          | (r1_tarski @ (sk_C @ X1 @ X0) @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0))
% 0.37/0.56          | (r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ X0 @ X2)
% 0.37/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ X2 @ (k3_tarski @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X2 @ (sk_C @ X1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_setfam_1 @ X0) @ X2)
% 0.37/0.56          | ((X0) = (k1_xboole_0))
% 0.37/0.56          | (r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X2 @ (k1_setfam_1 @ X0)) @ (k3_tarski @ X0))
% 0.37/0.56          | (r1_tarski @ X0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_C @ X2 @ (k1_setfam_1 @ X0)) @ (k3_tarski @ X0))
% 0.37/0.56          | (r1_tarski @ X0 @ X1)
% 0.37/0.56          | ((X0) = (k1_xboole_0))
% 0.37/0.56          | (r1_tarski @ (k1_setfam_1 @ X0) @ X2))),
% 0.37/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0))
% 0.37/0.56          | ((X0) = (k1_xboole_0))
% 0.37/0.56          | (r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1)
% 0.37/0.56          | ((X0) = (k1_xboole_0))
% 0.37/0.56          | (r1_tarski @ (k1_setfam_1 @ X0) @ (k3_tarski @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.56  thf('23', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_A) @ (k3_tarski @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_A @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf(t135_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.37/0.56         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         (((X11) = (k1_xboole_0))
% 0.37/0.56          | ~ (r1_tarski @ X11 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.37/0.56  thf('26', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X14 : $i, X19 : $i]:
% 0.37/0.56         (((X19) != (k1_setfam_1 @ X14))
% 0.37/0.56          | ((X19) = (k1_xboole_0))
% 0.37/0.56          | ((X14) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.37/0.56  thf('29', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.56  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.56  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.56  thf('31', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.56  thf('36', plain, ($false),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '27', '29', '30', '31', '35'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
