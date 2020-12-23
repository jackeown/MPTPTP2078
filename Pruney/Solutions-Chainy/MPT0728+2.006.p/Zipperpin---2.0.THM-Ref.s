%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QRvlisrfJs

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:38 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 ( 387 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k2_xboole_0 @ X34 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X7 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QRvlisrfJs
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.33/2.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.54  % Solved by: fo/fo7.sh
% 2.33/2.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.54  % done 2511 iterations in 2.087s
% 2.33/2.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.54  % SZS output start Refutation
% 2.33/2.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.33/2.54  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.33/2.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.33/2.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.33/2.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.33/2.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.33/2.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.33/2.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.33/2.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.33/2.54  thf(t69_enumset1, axiom,
% 2.33/2.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.33/2.54  thf('0', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 2.33/2.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.33/2.54  thf(d10_xboole_0, axiom,
% 2.33/2.54    (![A:$i,B:$i]:
% 2.33/2.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.33/2.54  thf('1', plain,
% 2.33/2.54      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 2.33/2.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.54  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.33/2.54      inference('simplify', [status(thm)], ['1'])).
% 2.33/2.54  thf(t38_zfmisc_1, axiom,
% 2.33/2.54    (![A:$i,B:$i,C:$i]:
% 2.33/2.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 2.33/2.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 2.33/2.54  thf('3', plain,
% 2.33/2.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.33/2.54         ((r2_hidden @ X28 @ X29)
% 2.33/2.54          | ~ (r1_tarski @ (k2_tarski @ X28 @ X30) @ X29))),
% 2.33/2.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.33/2.54  thf('4', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 2.33/2.54      inference('sup-', [status(thm)], ['2', '3'])).
% 2.33/2.54  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.33/2.54      inference('sup+', [status(thm)], ['0', '4'])).
% 2.33/2.54  thf(t1_xboole_0, axiom,
% 2.33/2.54    (![A:$i,B:$i,C:$i]:
% 2.33/2.54     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 2.33/2.54       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 2.33/2.54  thf('6', plain,
% 2.33/2.54      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.33/2.54         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 2.33/2.54          | (r2_hidden @ X4 @ X5)
% 2.33/2.54          | ~ (r2_hidden @ X4 @ X7))),
% 2.33/2.54      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.33/2.54  thf('7', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i]:
% 2.33/2.54         ((r2_hidden @ X0 @ X1)
% 2.33/2.54          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.33/2.54      inference('sup-', [status(thm)], ['5', '6'])).
% 2.33/2.54  thf(d1_ordinal1, axiom,
% 2.33/2.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 2.33/2.54  thf('8', plain,
% 2.33/2.54      (![X34 : $i]:
% 2.33/2.54         ((k1_ordinal1 @ X34) = (k2_xboole_0 @ X34 @ (k1_tarski @ X34)))),
% 2.33/2.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.33/2.54  thf(t95_xboole_1, axiom,
% 2.33/2.54    (![A:$i,B:$i]:
% 2.33/2.54     ( ( k3_xboole_0 @ A @ B ) =
% 2.33/2.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.33/2.54  thf('9', plain,
% 2.33/2.54      (![X14 : $i, X15 : $i]:
% 2.33/2.54         ((k3_xboole_0 @ X14 @ X15)
% 2.33/2.54           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 2.33/2.54              (k2_xboole_0 @ X14 @ X15)))),
% 2.33/2.54      inference('cnf', [status(esa)], [t95_xboole_1])).
% 2.33/2.54  thf(d3_tarski, axiom,
% 2.33/2.54    (![A:$i,B:$i]:
% 2.33/2.54     ( ( r1_tarski @ A @ B ) <=>
% 2.33/2.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.33/2.54  thf('10', plain,
% 2.33/2.54      (![X1 : $i, X3 : $i]:
% 2.33/2.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.33/2.54      inference('cnf', [status(esa)], [d3_tarski])).
% 2.33/2.54  thf('11', plain,
% 2.33/2.54      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.33/2.54         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 2.33/2.54          | (r2_hidden @ X4 @ X7)
% 2.33/2.54          | ~ (r2_hidden @ X4 @ X5))),
% 2.33/2.54      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.33/2.54  thf('12', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.54         ((r1_tarski @ X0 @ X1)
% 2.33/2.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 2.33/2.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X2)))),
% 2.33/2.54      inference('sup-', [status(thm)], ['10', '11'])).
% 2.33/2.54  thf('13', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.54         ((r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 2.33/2.54           (k3_xboole_0 @ X1 @ X0))
% 2.33/2.54          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 2.33/2.54             (k2_xboole_0 @ X1 @ X0))
% 2.33/2.54          | (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2))),
% 2.33/2.54      inference('sup+', [status(thm)], ['9', '12'])).
% 2.33/2.54  thf(t29_xboole_1, axiom,
% 2.33/2.54    (![A:$i,B:$i,C:$i]:
% 2.33/2.54     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 2.33/2.54  thf('14', plain,
% 2.33/2.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.33/2.54         (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ (k2_xboole_0 @ X11 @ X13))),
% 2.33/2.54      inference('cnf', [status(esa)], [t29_xboole_1])).
% 2.33/2.54  thf('15', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.54         (~ (r2_hidden @ X0 @ X1)
% 2.33/2.54          | (r2_hidden @ X0 @ X2)
% 2.33/2.54          | ~ (r1_tarski @ X1 @ X2))),
% 2.33/2.54      inference('cnf', [status(esa)], [d3_tarski])).
% 2.33/2.54  thf('16', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.54         ((r2_hidden @ X3 @ (k2_xboole_0 @ X1 @ X0))
% 2.33/2.54          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.33/2.54      inference('sup-', [status(thm)], ['14', '15'])).
% 2.33/2.54  thf('17', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.54         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 2.33/2.54          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 2.33/2.54             (k2_xboole_0 @ X1 @ X0)))),
% 2.33/2.54      inference('clc', [status(thm)], ['13', '16'])).
% 2.33/2.54  thf('18', plain,
% 2.33/2.54      (![X1 : $i, X3 : $i]:
% 2.33/2.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.33/2.54      inference('cnf', [status(esa)], [d3_tarski])).
% 2.33/2.54  thf('19', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i]:
% 2.33/2.54         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 2.33/2.54          | (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 2.33/2.54      inference('sup-', [status(thm)], ['17', '18'])).
% 2.33/2.54  thf('20', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i]:
% 2.33/2.54         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 2.33/2.54      inference('simplify', [status(thm)], ['19'])).
% 2.33/2.54  thf('21', plain,
% 2.33/2.54      (![X0 : $i]:
% 2.33/2.54         (r1_tarski @ (k5_xboole_0 @ X0 @ (k1_tarski @ X0)) @ 
% 2.33/2.54          (k1_ordinal1 @ X0))),
% 2.33/2.54      inference('sup+', [status(thm)], ['8', '20'])).
% 2.33/2.54  thf('22', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.54         (~ (r2_hidden @ X0 @ X1)
% 2.33/2.54          | (r2_hidden @ X0 @ X2)
% 2.33/2.54          | ~ (r1_tarski @ X1 @ X2))),
% 2.33/2.54      inference('cnf', [status(esa)], [d3_tarski])).
% 2.33/2.54  thf('23', plain,
% 2.33/2.54      (![X0 : $i, X1 : $i]:
% 2.33/2.54         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.33/2.54          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ (k1_tarski @ X0))))),
% 2.33/2.54      inference('sup-', [status(thm)], ['21', '22'])).
% 2.33/2.54  thf('24', plain,
% 2.33/2.54      (![X0 : $i]:
% 2.33/2.54         ((r2_hidden @ X0 @ X0) | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 2.33/2.54      inference('sup-', [status(thm)], ['7', '23'])).
% 2.33/2.54  thf(t10_ordinal1, conjecture,
% 2.33/2.54    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 2.33/2.54  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.54    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 2.33/2.54    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 2.33/2.54  thf('25', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 2.33/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.54  thf('26', plain, ((r2_hidden @ sk_A @ sk_A)),
% 2.33/2.54      inference('sup-', [status(thm)], ['24', '25'])).
% 2.33/2.54  thf(t7_ordinal1, axiom,
% 2.33/2.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.33/2.54  thf('27', plain,
% 2.33/2.54      (![X35 : $i, X36 : $i]:
% 2.33/2.54         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 2.33/2.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.33/2.54  thf('28', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 2.33/2.54      inference('sup-', [status(thm)], ['26', '27'])).
% 2.33/2.54  thf('29', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.33/2.54      inference('simplify', [status(thm)], ['1'])).
% 2.33/2.54  thf('30', plain, ($false), inference('demod', [status(thm)], ['28', '29'])).
% 2.33/2.54  
% 2.33/2.54  % SZS output end Refutation
% 2.33/2.54  
% 2.33/2.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
