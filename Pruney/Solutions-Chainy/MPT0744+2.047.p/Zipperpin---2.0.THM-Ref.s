%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.we5uri0z94

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 122 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  472 ( 920 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(reflexivity_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( r1_ordinal1 @ A @ A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_ordinal1 @ X10 @ X10 )
      | ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_ordinal1])).

thf('3',plain,
    ( ! [X10: $i] :
        ( ( r1_ordinal1 @ X10 @ X10 )
        | ~ ( v3_ordinal1 @ X10 ) )
   <= ! [X10: $i] :
        ( ( r1_ordinal1 @ X10 @ X10 )
        | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    v3_ordinal1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X11: $i] :
        ~ ( v3_ordinal1 @ X11 )
   <= ! [X11: $i] :
        ~ ( v3_ordinal1 @ X11 ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,(
    ~ ! [X11: $i] :
        ~ ( v3_ordinal1 @ X11 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X10: $i] :
        ( ( r1_ordinal1 @ X10 @ X10 )
        | ~ ( v3_ordinal1 @ X10 ) )
    | ! [X11: $i] :
        ~ ( v3_ordinal1 @ X11 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( r1_ordinal1 @ X10 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference('sat_resolution*',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( r1_ordinal1 @ X10 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(simpl_trail,[status(thm)],['3','8'])).

thf('10',plain,
    ( ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_ordinal1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A_1 @ sk_B_1 )
      | ( sk_A_1 = sk_B_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('15',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('18',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r1_tarski @ sk_A_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('21',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( sk_A_1 = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
      & ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_A_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
      & ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v3_ordinal1 @ sk_A_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
      & ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_ordinal1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('35',plain,
    ( ( ( r1_tarski @ sk_A_1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A_1 ) )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_tarski @ sk_A_1 @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('40',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r2_xboole_0 @ sk_A_1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_xboole_0 @ X17 @ X16 )
      | ~ ( v1_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('42',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A_1 )
      | ( r2_hidden @ sk_A_1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('45',plain,(
    v1_ordinal1 @ sk_A_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r2_hidden @ sk_A_1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('49',plain,
    ( ( ( sk_A_1 = sk_B_1 )
      | ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) )
   <= ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( sk_A_1 = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_A_1 ) )
   <= ( ~ ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ sk_A_1 @ sk_B_1 )
    | ( r2_hidden @ sk_A_1 @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.we5uri0z94
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 98 iterations in 0.042s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.49  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.49  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.49  thf(t34_ordinal1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.49             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.49                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r1_ordinal1 @ sk_A_1 @ sk_B_1)
% 0.21/0.49        | ~ (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)) | 
% 0.21/0.49       ~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(reflexivity_r1_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) => ( r1_ordinal1 @ A @ A ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((r1_ordinal1 @ X10 @ X10)
% 0.21/0.49          | ~ (v3_ordinal1 @ X10)
% 0.21/0.49          | ~ (v3_ordinal1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [reflexivity_r1_ordinal1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((![X10 : $i]: ((r1_ordinal1 @ X10 @ X10) | ~ (v3_ordinal1 @ X10)))
% 0.21/0.49         <= ((![X10 : $i]: ((r1_ordinal1 @ X10 @ X10) | ~ (v3_ordinal1 @ X10))))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain, ((v3_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((![X11 : $i]: ~ (v3_ordinal1 @ X11))
% 0.21/0.49         <= ((![X11 : $i]: ~ (v3_ordinal1 @ X11)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('6', plain, (~ (![X11 : $i]: ~ (v3_ordinal1 @ X11))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((![X10 : $i]: ((r1_ordinal1 @ X10 @ X10) | ~ (v3_ordinal1 @ X10))) | 
% 0.21/0.49       (![X11 : $i]: ~ (v3_ordinal1 @ X11))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((![X10 : $i]: ((r1_ordinal1 @ X10 @ X10) | ~ (v3_ordinal1 @ X10)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X10 : $i]: ((r1_ordinal1 @ X10 @ X10) | ~ (v3_ordinal1 @ X10))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['3', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r1_ordinal1 @ sk_A_1 @ sk_B_1)
% 0.21/0.49        | (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['10'])).
% 0.21/0.49  thf(t13_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((X14) = (X13))
% 0.21/0.49          | (r2_hidden @ X14 @ X13)
% 0.21/0.49          | ~ (r2_hidden @ X14 @ (k1_ordinal1 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((r2_hidden @ sk_A_1 @ sk_B_1) | ((sk_A_1) = (sk_B_1))))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(d2_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.49       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.49          | (r1_tarski @ X5 @ X6)
% 0.21/0.49          | ~ (v1_ordinal1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1))
% 0.21/0.49         | ~ (v1_ordinal1 @ sk_B_1)
% 0.21/0.49         | (r1_tarski @ sk_A_1 @ sk_B_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.49  thf('17', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.49  thf('18', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1)) | (r1_tarski @ sk_A_1 @ sk_B_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.49  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.49       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X8)
% 0.21/0.49          | ~ (v3_ordinal1 @ X9)
% 0.21/0.49          | (r1_ordinal1 @ X8 @ X9)
% 0.21/0.49          | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1))
% 0.21/0.49         | (r1_ordinal1 @ sk_A_1 @ sk_B_1)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_A_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, ((v3_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1)) | (r1_ordinal1 @ sk_A_1 @ sk_B_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (r1_ordinal1 @ sk_A_1 @ sk_B_1))
% 0.21/0.49         <= (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((sk_A_1) = (sk_B_1)))
% 0.21/0.49         <= (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)) & 
% 0.21/0.49             ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (r1_ordinal1 @ sk_A_1 @ sk_B_1))
% 0.21/0.49         <= (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((~ (r1_ordinal1 @ sk_A_1 @ sk_A_1))
% 0.21/0.49         <= (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)) & 
% 0.21/0.49             ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (v3_ordinal1 @ sk_A_1))
% 0.21/0.49         <= (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)) & 
% 0.21/0.49             ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '28'])).
% 0.21/0.49  thf('30', plain, ((v3_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((r1_ordinal1 @ sk_A_1 @ sk_B_1)) | 
% 0.21/0.49       ~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r1_ordinal1 @ sk_A_1 @ sk_B_1)) | 
% 0.21/0.49       ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['10'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((r1_ordinal1 @ sk_A_1 @ sk_B_1)) <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['10'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X8)
% 0.21/0.49          | ~ (v3_ordinal1 @ X9)
% 0.21/0.49          | (r1_tarski @ X8 @ X9)
% 0.21/0.49          | ~ (r1_ordinal1 @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((r1_tarski @ sk_A_1 @ sk_B_1)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_A_1))) <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain, ((v3_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((r1_tarski @ sk_A_1 @ sk_B_1)) <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.49  thf(d8_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1)) | (r2_xboole_0 @ sk_A_1 @ sk_B_1)))
% 0.21/0.49         <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf(t21_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X16)
% 0.21/0.49          | (r2_hidden @ X17 @ X16)
% 0.21/0.49          | ~ (r2_xboole_0 @ X17 @ X16)
% 0.21/0.49          | ~ (v1_ordinal1 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1))
% 0.21/0.49         | ~ (v1_ordinal1 @ sk_A_1)
% 0.21/0.49         | (r2_hidden @ sk_A_1 @ sk_B_1)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((v3_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.49  thf('45', plain, ((v1_ordinal1 @ sk_A_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1)) | (r2_hidden @ sk_A_1 @ sk_B_1)))
% 0.21/0.49         <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         ((r2_hidden @ X14 @ (k1_ordinal1 @ X15)) | ~ (r2_hidden @ X14 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((((sk_A_1) = (sk_B_1)) | (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))
% 0.21/0.49         <= (((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.49         <= (~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((((sk_A_1) = (sk_B_1)))
% 0.21/0.49         <= (~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.49             ((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.49         <= (~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_A_1)))
% 0.21/0.49         <= (~ ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.49             ((r1_ordinal1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.49  thf('54', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_ordinal1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (~ ((r1_ordinal1 @ sk_A_1 @ sk_B_1)) | 
% 0.21/0.49       ((r2_hidden @ sk_A_1 @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '31', '32', '55'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
