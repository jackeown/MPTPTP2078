%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQfxLxGUYY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:54 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  391 ( 710 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','18','21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('26',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQfxLxGUYY
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.87/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.07  % Solved by: fo/fo7.sh
% 0.87/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.07  % done 647 iterations in 0.619s
% 0.87/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.07  % SZS output start Refutation
% 0.87/1.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.87/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.87/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.07  thf(t45_zfmisc_1, conjecture,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.87/1.07       ( r2_hidden @ A @ B ) ))).
% 0.87/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.07    (~( ![A:$i,B:$i]:
% 0.87/1.07        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.87/1.07          ( r2_hidden @ A @ B ) ) )),
% 0.87/1.07    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.87/1.07  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('1', plain,
% 0.87/1.07      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t28_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.87/1.07  thf('2', plain,
% 0.87/1.07      (![X7 : $i, X8 : $i]:
% 0.87/1.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.87/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.07  thf('3', plain,
% 0.87/1.07      (((k3_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 0.87/1.07         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.87/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.87/1.07  thf(commutativity_k3_xboole_0, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.87/1.07  thf('4', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.07  thf('5', plain,
% 0.87/1.07      (((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.87/1.07         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.87/1.07      inference('demod', [status(thm)], ['3', '4'])).
% 0.87/1.07  thf(t94_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k2_xboole_0 @ A @ B ) =
% 0.87/1.07       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.87/1.07  thf('6', plain,
% 0.87/1.07      (![X14 : $i, X15 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.07           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.87/1.07              (k3_xboole_0 @ X14 @ X15)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.87/1.07  thf(t91_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.87/1.07       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.87/1.07  thf('7', plain,
% 0.87/1.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.87/1.07         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.87/1.07           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.87/1.07  thf('8', plain,
% 0.87/1.07      (![X14 : $i, X15 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.07           = (k5_xboole_0 @ X14 @ 
% 0.87/1.07              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.87/1.07      inference('demod', [status(thm)], ['6', '7'])).
% 0.87/1.07  thf('9', plain,
% 0.87/1.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.87/1.07         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.87/1.07           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.87/1.07  thf(commutativity_k5_xboole_0, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.87/1.07  thf('10', plain,
% 0.87/1.07      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.87/1.07      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.87/1.07  thf('11', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.07         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.87/1.07           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['9', '10'])).
% 0.87/1.07  thf('12', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X1 @ X0)
% 0.87/1.07           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['8', '11'])).
% 0.87/1.07  thf('13', plain,
% 0.87/1.07      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.87/1.07      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.87/1.07  thf('14', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X1 @ X0)
% 0.87/1.07           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.87/1.07      inference('demod', [status(thm)], ['12', '13'])).
% 0.87/1.07  thf('15', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.07  thf('16', plain,
% 0.87/1.07      (![X14 : $i, X15 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.07           = (k5_xboole_0 @ X14 @ 
% 0.87/1.07              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.87/1.07      inference('demod', [status(thm)], ['6', '7'])).
% 0.87/1.07  thf('17', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X0 @ X1)
% 0.87/1.07           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['15', '16'])).
% 0.87/1.07  thf('18', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['14', '17'])).
% 0.87/1.07  thf(t7_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.87/1.07  thf('19', plain,
% 0.87/1.07      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.87/1.07      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.87/1.07  thf('20', plain,
% 0.87/1.07      (![X7 : $i, X8 : $i]:
% 0.87/1.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.87/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.07  thf('21', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.87/1.07      inference('sup-', [status(thm)], ['19', '20'])).
% 0.87/1.07  thf('22', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['14', '17'])).
% 0.87/1.07  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.87/1.07      inference('demod', [status(thm)], ['5', '18', '21', '22'])).
% 0.87/1.07  thf(t69_enumset1, axiom,
% 0.87/1.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.87/1.07  thf('24', plain,
% 0.87/1.07      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.87/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.87/1.07  thf(l45_zfmisc_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.87/1.07       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.87/1.07            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.87/1.07  thf('25', plain,
% 0.87/1.07      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.87/1.07         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.87/1.07          | ((X46) != (k1_tarski @ X44)))),
% 0.87/1.07      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.87/1.07  thf('26', plain,
% 0.87/1.07      (![X44 : $i, X47 : $i]:
% 0.87/1.07         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X47))),
% 0.87/1.07      inference('simplify', [status(thm)], ['25'])).
% 0.87/1.07  thf('27', plain,
% 0.87/1.07      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['24', '26'])).
% 0.87/1.07  thf(t10_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.87/1.07  thf('28', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.87/1.07         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.87/1.07  thf('29', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (r1_tarski @ (k1_tarski @ X0) @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['27', '28'])).
% 0.87/1.07  thf('30', plain,
% 0.87/1.07      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.87/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.87/1.07  thf(t38_zfmisc_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.87/1.07       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.87/1.07  thf('31', plain,
% 0.87/1.07      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.87/1.07         ((r2_hidden @ X50 @ X51)
% 0.87/1.07          | ~ (r1_tarski @ (k2_tarski @ X50 @ X52) @ X51))),
% 0.87/1.07      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.87/1.07  thf('32', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.87/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.87/1.07  thf('33', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['29', '32'])).
% 0.87/1.07  thf('34', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.87/1.07      inference('sup+', [status(thm)], ['23', '33'])).
% 0.87/1.07  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.87/1.07  
% 0.87/1.07  % SZS output end Refutation
% 0.87/1.07  
% 0.93/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
