%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NoCT26BjFQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:07 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 239 expanded)
%              Number of leaves         :   31 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  528 (1708 expanded)
%              Number of equality atoms :   65 ( 236 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X60: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X60 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( X25 = X22 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('38',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r2_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('49',plain,
    ( ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NoCT26BjFQ
% 0.16/0.37  % Computer   : n007.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:49:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 297 iterations in 0.118s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.60  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(t7_xboole_0, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.60  thf(t66_zfmisc_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.37/0.60          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.37/0.60             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(t95_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k3_xboole_0 @ A @ B ) =
% 0.37/0.60       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X20 @ X21)
% 0.37/0.60           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.37/0.60              (k2_xboole_0 @ X20 @ X21)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.37/0.60  thf(t91_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.60           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X20 @ X21)
% 0.37/0.60           = (k5_xboole_0 @ X20 @ 
% 0.37/0.60              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.37/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf(t92_xboole_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.60  thf('5', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.60           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.60  thf('8', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X20 @ X21)
% 0.37/0.60           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.37/0.60              (k2_xboole_0 @ X20 @ X21)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X0 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.60  thf('11', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.60  thf(t69_enumset1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.37/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.60  thf(t31_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.37/0.60  thf('13', plain, (![X60 : $i]: ((k3_tarski @ (k1_tarski @ X60)) = (X60))),
% 0.37/0.60      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.37/0.60  thf('14', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf(l51_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X58 : $i, X59 : $i]:
% 0.37/0.60         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.37/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.60  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf('17', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['7', '17'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['4', '18'])).
% 0.37/0.60  thf(t100_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X9 : $i, X10 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X9 @ X10)
% 0.37/0.60           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.60           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['7', '17'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.60         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['1', '23'])).
% 0.37/0.60  thf(t5_boole, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.60  thf('25', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.60  thf(t7_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.60  thf('28', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf(d3_tarski, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.60          | (r2_hidden @ X0 @ X2)
% 0.37/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      ((((sk_A) = (k1_xboole_0))
% 0.37/0.60        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['0', '30'])).
% 0.37/0.60  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('33', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf(d1_tarski, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X25 @ X24)
% 0.37/0.60          | ((X25) = (X22))
% 0.37/0.60          | ((X24) != (k1_tarski @ X22)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X22 : $i, X25 : $i]:
% 0.37/0.60         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.60  thf('36', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['33', '35'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.60  thf(l1_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X55 : $i, X57 : $i]:
% 0.37/0.60         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 0.37/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.60  thf(t60_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X12 @ X13) | ~ (r2_xboole_0 @ X13 @ X12))),
% 0.37/0.60      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((X0) = (k1_xboole_0))
% 0.37/0.60          | ~ (r2_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      ((~ (r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '41'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.60  thf(d8_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.60       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (![X4 : $i, X6 : $i]:
% 0.37/0.60         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.60      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.60  thf('46', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.37/0.60          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.60        | ((sk_A) = (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.37/0.60      inference('sup+', [status(thm)], ['43', '46'])).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.60        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.60  thf('50', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('51', plain, ((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.37/0.60  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['42', '51'])).
% 0.37/0.60  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('54', plain, ($false),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
