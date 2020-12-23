%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WqE3kBtfa8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 104 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 ( 587 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('0',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ X13 @ sk_A )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(reflexivity_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( r1_ordinal1 @ A @ A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_ordinal1 @ X3 @ X3 )
      | ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_ordinal1])).

thf('4',plain,
    ( ! [X3: $i] :
        ( ( r1_ordinal1 @ X3 @ X3 )
        | ~ ( v3_ordinal1 @ X3 ) )
   <= ! [X3: $i] :
        ( ( r1_ordinal1 @ X3 @ X3 )
        | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t31_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( v3_ordinal1 @ B )
            & ( r1_tarski @ B @ A ) ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( v3_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t31_ordinal1])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 )
   <= ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( v3_ordinal1 @ sk_A )
   <= ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 )
   <= ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,(
    ~ ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X3: $i] :
        ( ( r1_ordinal1 @ X3 @ X3 )
        | ~ ( v3_ordinal1 @ X3 ) )
    | ! [X4: $i] :
        ~ ( v3_ordinal1 @ X4 ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( r1_ordinal1 @ X3 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( r1_ordinal1 @ X3 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(simpl_trail,[status(thm)],['4','13'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ X8 ) @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('24',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t35_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X9 ) )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v3_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('29',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X9 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('31',plain,(
    v3_ordinal1 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['24','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WqE3kBtfa8
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 28 iterations in 0.016s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.49  thf(t37_ordinal1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t37_ordinal1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X13 : $i]: ((r2_hidden @ X13 @ sk_A) | ~ (v3_ordinal1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l49_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v3_ordinal1 @ X0) | (r1_tarski @ X0 @ (k3_tarski @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(reflexivity_r1_ordinal1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) => ( r1_ordinal1 @ A @ A ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3) | ~ (v3_ordinal1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [reflexivity_r1_ordinal1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((![X3 : $i]: ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3)))
% 0.20/0.49         <= ((![X3 : $i]: ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(t31_ordinal1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ![B:$i]:
% 0.20/0.49         ( ( r2_hidden @ B @ A ) =>
% 0.20/0.49           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.20/0.49       ( v3_ordinal1 @ A ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X6 : $i]: ((v3_ordinal1 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t31_ordinal1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X12 : $i]: ((v3_ordinal1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain, (((v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((![X4 : $i]: ~ (v3_ordinal1 @ X4))
% 0.20/0.49         <= ((![X4 : $i]: ~ (v3_ordinal1 @ X4)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((v3_ordinal1 @ sk_A)) <= ((![X4 : $i]: ~ (v3_ordinal1 @ X4)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((![X4 : $i]: ~ (v3_ordinal1 @ X4))
% 0.20/0.49         <= ((![X4 : $i]: ~ (v3_ordinal1 @ X4)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('11', plain, (~ (![X4 : $i]: ~ (v3_ordinal1 @ X4))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((![X3 : $i]: ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3))) | 
% 0.20/0.49       (![X4 : $i]: ~ (v3_ordinal1 @ X4))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((![X3 : $i]: ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X3 : $i]: ((r1_ordinal1 @ X3 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['4', '13'])).
% 0.20/0.49  thf(t33_ordinal1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.49           ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.49             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (v3_ordinal1 @ X7)
% 0.20/0.49          | ~ (r1_ordinal1 @ (k1_ordinal1 @ X8) @ X7)
% 0.20/0.49          | (r2_hidden @ X8 @ X7)
% 0.20/0.49          | ~ (v3_ordinal1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.20/0.49          | ~ (v3_ordinal1 @ X0)
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 0.20/0.49          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 0.20/0.49          | ~ (v3_ordinal1 @ X0)
% 0.20/0.49          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf(t29_ordinal1, axiom,
% 0.20/0.49    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X5 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v3_ordinal1 @ X0) | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf(t7_ordinal1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v3_ordinal1 @ X0) | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (k3_tarski @ sk_A)))
% 0.20/0.49        | ~ (v3_ordinal1 @ (k3_tarski @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X5 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.49  thf('24', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf(t35_ordinal1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) =>
% 0.20/0.49       ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         ((v3_ordinal1 @ (k3_tarski @ X9)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X12 : $i]: ((v3_ordinal1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((v3_ordinal1 @ (k3_tarski @ sk_A)) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('29', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         ((v3_ordinal1 @ (k3_tarski @ X9)) | ~ (v3_ordinal1 @ (sk_B_1 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.20/0.49  thf('31', plain, ((v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, ($false), inference('demod', [status(thm)], ['24', '31'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
