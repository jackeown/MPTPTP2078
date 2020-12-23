%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3wIB05IDj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 148 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  458 (1085 expanded)
%              Number of equality atoms :   38 (  74 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r2_hidden @ X90 @ X89 )
      | ~ ( r1_tarski @ ( k2_tarski @ X88 @ X90 ) @ X89 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r2_hidden @ X88 @ X89 )
      | ~ ( r1_tarski @ ( k2_tarski @ X88 @ X90 ) @ X89 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X88: $i,X90: $i,X91: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X88 @ X90 ) @ X91 )
      | ~ ( r2_hidden @ X90 @ X91 )
      | ~ ( r2_hidden @ X88 @ X91 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','21','22','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','41'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('44',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r2_hidden @ X88 @ X89 )
      | ~ ( r1_tarski @ ( k2_tarski @ X88 @ X90 ) @ X89 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('46',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3wIB05IDj
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 213 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(t47_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.20/0.54       ( r2_hidden @ A @ C ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.20/0.54          ( r2_hidden @ A @ C ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.20/0.54  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X4 : $i, X6 : $i]:
% 0.20/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.54        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.54  thf(t38_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X88 : $i, X89 : $i, X90 : $i]:
% 0.20/0.54         ((r2_hidden @ X90 @ X89)
% 0.20/0.54          | ~ (r1_tarski @ (k2_tarski @ X88 @ X90) @ X89))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X88 : $i, X89 : $i, X90 : $i]:
% 0.20/0.54         ((r2_hidden @ X88 @ X89)
% 0.20/0.54          | ~ (r1_tarski @ (k2_tarski @ X88 @ X90) @ X89))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X88 : $i, X90 : $i, X91 : $i]:
% 0.20/0.54         ((r1_tarski @ (k2_tarski @ X88 @ X90) @ X91)
% 0.20/0.54          | ~ (r2_hidden @ X90 @ X91)
% 0.20/0.54          | ~ (r2_hidden @ X88 @ X91))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.54          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X4 : $i, X6 : $i]:
% 0.20/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.20/0.54          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf(l51_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X86 : $i, X87 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X86 : $i, X87 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf(t7_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.20/0.54  thf(t95_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.20/0.54           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.20/0.54              (k2_xboole_0 @ X17 @ X18)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.54  thf(t91_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.54           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.20/0.54           = (k5_xboole_0 @ X17 @ 
% 0.20/0.54              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54         = (k5_xboole_0 @ sk_C @ 
% 0.20/0.54            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.54  thf(t5_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('31', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.54  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.20/0.54           = (k5_xboole_0 @ X17 @ 
% 0.20/0.54              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.54           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf(t2_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.54  thf(t1_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('36', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('37', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.54           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54         = (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29', '41'])).
% 0.20/0.54  thf(t17_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.54  thf('44', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.54      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X88 : $i, X89 : $i, X90 : $i]:
% 0.20/0.54         ((r2_hidden @ X88 @ X89)
% 0.20/0.54          | ~ (r1_tarski @ (k2_tarski @ X88 @ X90) @ X89))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('46', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
