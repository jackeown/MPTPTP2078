%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0wmAEfgspR

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 111 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  451 ( 742 expanded)
%              Number of equality atoms :   62 ( 101 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X61 @ X60 ) @ X60 )
      | ( r1_tarski @ X61 @ ( k1_setfam_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X57 != X56 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X57 ) @ ( k1_tarski @ X56 ) )
       != ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X56: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X56 ) )
     != ( k1_tarski @ X56 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X56: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X56 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('27',plain,(
    ! [X59: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X59 ) @ ( k3_tarski @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( r1_tarski @ X61 @ ( sk_C_1 @ X61 @ X60 ) )
      | ( r1_tarski @ X61 @ ( k1_setfam_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X56: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X56 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0wmAEfgspR
% 0.15/0.37  % Computer   : n025.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:50:20 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 268 iterations in 0.116s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.42/0.60  thf(t11_setfam_1, conjecture,
% 0.42/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.42/0.60  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t6_setfam_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.42/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X60 : $i, X61 : $i]:
% 0.42/0.60         (((X60) = (k1_xboole_0))
% 0.42/0.60          | (r2_hidden @ (sk_C_1 @ X61 @ X60) @ X60)
% 0.42/0.60          | (r1_tarski @ X61 @ (k1_setfam_1 @ X60)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.42/0.60  thf(d1_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X16 @ X15)
% 0.42/0.60          | ((X16) = (X13))
% 0.42/0.60          | ((X15) != (k1_tarski @ X13)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X13 : $i, X16 : $i]:
% 0.42/0.60         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.42/0.60          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '3'])).
% 0.42/0.60  thf(t20_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.60         ( k1_tarski @ A ) ) <=>
% 0.42/0.60       ( ( A ) != ( B ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X56 : $i, X57 : $i]:
% 0.42/0.60         (((X57) != (X56))
% 0.42/0.60          | ((k4_xboole_0 @ (k1_tarski @ X57) @ (k1_tarski @ X56))
% 0.42/0.60              != (k1_tarski @ X57)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X56 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ (k1_tarski @ X56) @ (k1_tarski @ X56))
% 0.42/0.60           != (k1_tarski @ X56))),
% 0.42/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.42/0.60  thf(idempotence_k2_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.60  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.42/0.60  thf(t95_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k3_xboole_0 @ A @ B ) =
% 0.42/0.60       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X11 @ X12)
% 0.42/0.60           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.42/0.60              (k2_xboole_0 @ X11 @ X12)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.42/0.60  thf(t91_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.42/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.42/0.60           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X11 @ X12)
% 0.42/0.60           = (k5_xboole_0 @ X11 @ 
% 0.42/0.60              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.42/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X0 @ X0)
% 0.42/0.60           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['7', '10'])).
% 0.42/0.60  thf(t92_xboole_1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.42/0.60  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.42/0.60  thf(t5_boole, axiom,
% 0.42/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.60  thf('14', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.42/0.60  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.60  thf(t100_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X4 @ X5)
% 0.42/0.60           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.42/0.60  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain, (![X56 : $i]: ((k1_xboole_0) != (k1_tarski @ X56))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '19'])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.42/0.60          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('clc', [status(thm)], ['4', '20'])).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf(l51_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X54 : $i, X55 : $i]:
% 0.42/0.60         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.42/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.42/0.60  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.42/0.60  thf('26', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf(t3_setfam_1, axiom,
% 0.42/0.60    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X59 : $i]: (r1_tarski @ (k1_setfam_1 @ X59) @ (k3_tarski @ X59))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.42/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf(d10_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X1 : $i, X3 : $i]:
% 0.42/0.60         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((sk_C_1 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.42/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '30'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X60 : $i, X61 : $i]:
% 0.42/0.60         (((X60) = (k1_xboole_0))
% 0.42/0.60          | ~ (r1_tarski @ X61 @ (sk_C_1 @ X61 @ X60))
% 0.42/0.60          | (r1_tarski @ X61 @ (k1_setfam_1 @ X60)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X0 @ X0)
% 0.42/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.60  thf('35', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.42/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '35'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.42/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.42/0.60          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('clc', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain, (![X56 : $i]: ((k1_xboole_0) != (k1_tarski @ X56))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '19'])).
% 0.42/0.60  thf('40', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['38', '39'])).
% 0.42/0.60  thf('41', plain, (((sk_A) != (sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '40'])).
% 0.42/0.60  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
