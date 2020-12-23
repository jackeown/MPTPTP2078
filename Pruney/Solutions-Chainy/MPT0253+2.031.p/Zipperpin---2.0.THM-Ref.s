%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oBRH502CsN

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:34 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 154 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  543 (1260 expanded)
%              Number of equality atoms :   54 ( 124 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['12','17','18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['12','17','18','19'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['12','17','18','19'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,
    ( sk_B
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','39'])).

thf('41',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['12','17','18','19'])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k5_xboole_0 @ k1_xboole_0 @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['41','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oBRH502CsN
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.66/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.87  % Solved by: fo/fo7.sh
% 0.66/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.87  % done 209 iterations in 0.429s
% 0.66/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.87  % SZS output start Refutation
% 0.66/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.87  thf(t48_zfmisc_1, conjecture,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.66/0.87       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.66/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.87        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.66/0.87          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.66/0.87    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.66/0.87  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(t38_zfmisc_1, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.66/0.87       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.66/0.87  thf('2', plain,
% 0.66/0.87      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.66/0.87         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 0.66/0.87          | ~ (r2_hidden @ X48 @ X49)
% 0.66/0.87          | ~ (r2_hidden @ X46 @ X49))),
% 0.66/0.87      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.66/0.87  thf('3', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (r2_hidden @ X0 @ sk_B)
% 0.66/0.87          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.87  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.66/0.87      inference('sup-', [status(thm)], ['0', '3'])).
% 0.66/0.87  thf(l32_xboole_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.87  thf('5', plain,
% 0.66/0.87      (![X4 : $i, X6 : $i]:
% 0.66/0.87         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.87  thf('6', plain,
% 0.66/0.87      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.66/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.66/0.87  thf(t39_xboole_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.87  thf('7', plain,
% 0.66/0.87      (![X10 : $i, X11 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.66/0.87           = (k2_xboole_0 @ X10 @ X11))),
% 0.66/0.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.66/0.87  thf('8', plain,
% 0.66/0.87      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.66/0.87         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['6', '7'])).
% 0.66/0.87  thf(t1_boole, axiom,
% 0.66/0.87    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.87  thf('9', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.66/0.87      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.87  thf('10', plain,
% 0.66/0.87      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A)))),
% 0.66/0.87      inference('demod', [status(thm)], ['8', '9'])).
% 0.66/0.87  thf('11', plain,
% 0.66/0.87      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.66/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.66/0.87  thf(t94_xboole_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( k2_xboole_0 @ A @ B ) =
% 0.66/0.87       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.87  thf('12', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X15 @ X16)
% 0.66/0.87           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 0.66/0.87              (k3_xboole_0 @ X15 @ X16)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.66/0.87  thf(t91_xboole_1, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.87       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.87  thf('13', plain,
% 0.66/0.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.87           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.87  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.87    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.87  thf('14', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('15', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.66/0.87           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.87  thf('16', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('17', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 0.66/0.87           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['15', '16'])).
% 0.66/0.87  thf('18', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf(t100_xboole_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.87  thf('19', plain,
% 0.66/0.87      (![X7 : $i, X8 : $i]:
% 0.66/0.87         ((k4_xboole_0 @ X7 @ X8)
% 0.66/0.87           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.87  thf('20', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X15 @ X16)
% 0.66/0.87           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.66/0.87      inference('demod', [status(thm)], ['12', '17', '18', '19'])).
% 0.66/0.87  thf('21', plain,
% 0.66/0.87      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B)
% 0.66/0.87         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.66/0.87      inference('sup+', [status(thm)], ['11', '20'])).
% 0.66/0.87  thf('22', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('23', plain,
% 0.66/0.87      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B)
% 0.66/0.87         = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.87  thf('24', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.87  thf('25', plain,
% 0.66/0.87      (![X7 : $i, X8 : $i]:
% 0.66/0.87         ((k4_xboole_0 @ X7 @ X8)
% 0.66/0.87           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.87  thf('26', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i]:
% 0.66/0.87         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.87  thf('27', plain,
% 0.66/0.87      (![X7 : $i, X8 : $i]:
% 0.66/0.87         ((k4_xboole_0 @ X7 @ X8)
% 0.66/0.87           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.87  thf('28', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('29', plain,
% 0.66/0.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.87           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.87  thf('30', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.87           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.66/0.87  thf('31', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.87           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['27', '30'])).
% 0.66/0.87  thf('32', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.66/0.87           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['13', '14'])).
% 0.66/0.87  thf('33', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.87           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.66/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.66/0.87  thf('34', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i]:
% 0.66/0.87         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.66/0.87           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['26', '33'])).
% 0.66/0.87  thf('35', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('36', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X15 @ X16)
% 0.66/0.87           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.66/0.87      inference('demod', [status(thm)], ['12', '17', '18', '19'])).
% 0.66/0.87  thf('37', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X15 @ X16)
% 0.66/0.87           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.66/0.87      inference('demod', [status(thm)], ['12', '17', '18', '19'])).
% 0.66/0.87  thf('38', plain,
% 0.66/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.66/0.87      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.66/0.87  thf('39', plain,
% 0.66/0.87      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.66/0.87         = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['23', '38'])).
% 0.66/0.87  thf('40', plain, (((sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.66/0.87      inference('sup+', [status(thm)], ['10', '39'])).
% 0.66/0.87  thf('41', plain,
% 0.66/0.87      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('42', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('43', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('44', plain,
% 0.66/0.87      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.66/0.87         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 0.66/0.87          | ~ (r2_hidden @ X48 @ X49)
% 0.66/0.87          | ~ (r2_hidden @ X46 @ X49))),
% 0.66/0.87      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.66/0.87  thf('45', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (r2_hidden @ X0 @ sk_B)
% 0.66/0.87          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.87  thf('46', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.66/0.87      inference('sup-', [status(thm)], ['42', '45'])).
% 0.66/0.87  thf('47', plain,
% 0.66/0.87      (![X4 : $i, X6 : $i]:
% 0.66/0.87         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.87  thf('48', plain,
% 0.66/0.87      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.66/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.66/0.87  thf('49', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i]:
% 0.66/0.87         ((k2_xboole_0 @ X15 @ X16)
% 0.66/0.87           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.66/0.87      inference('demod', [status(thm)], ['12', '17', '18', '19'])).
% 0.66/0.87  thf('50', plain,
% 0.66/0.87      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.66/0.87         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.66/0.87      inference('sup+', [status(thm)], ['48', '49'])).
% 0.66/0.87  thf('51', plain,
% 0.66/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.87  thf('52', plain,
% 0.66/0.87      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.66/0.87         = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['50', '51'])).
% 0.66/0.87  thf('53', plain, (((k5_xboole_0 @ k1_xboole_0 @ sk_B) != (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['41', '52'])).
% 0.66/0.87  thf('54', plain, ($false),
% 0.66/0.87      inference('simplify_reflect-', [status(thm)], ['40', '53'])).
% 0.66/0.87  
% 0.66/0.87  % SZS output end Refutation
% 0.66/0.87  
% 0.66/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
