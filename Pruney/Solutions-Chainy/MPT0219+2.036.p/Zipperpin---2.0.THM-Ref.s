%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dgEzpm4tLe

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:08 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 160 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  461 (1120 expanded)
%              Number of equality atoms :   50 ( 107 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42 = X41 )
      | ~ ( r1_tarski @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('45',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dgEzpm4tLe
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 766 iterations in 0.305s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(t13_zfmisc_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.55/0.74         ( k1_tarski @ A ) ) =>
% 0.55/0.74       ( ( A ) = ( B ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i]:
% 0.55/0.74        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.55/0.74            ( k1_tarski @ A ) ) =>
% 0.55/0.74          ( ( A ) = ( B ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.55/0.74         = (k1_tarski @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t98_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.74  thf(idempotence_k3_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.55/0.74  thf('2', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.74  thf(t100_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.55/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.74  thf(t79_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.55/0.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.55/0.74  thf(t4_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X5 @ X6)
% 0.55/0.74          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.55/0.74          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['6', '9'])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['5', '10'])).
% 0.55/0.74  thf(t7_xboole_0, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.55/0.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.55/0.74          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['11', '14'])).
% 0.55/0.74  thf(t36_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf(t28_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X14 : $i, X15 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.55/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.55/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.74  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['15', '20'])).
% 0.55/0.74  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['4', '21'])).
% 0.55/0.74  thf(t91_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.55/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.55/0.74           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.55/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['22', '23'])).
% 0.55/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf(t5_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.74  thf('26', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['25', '26'])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['1', '28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['0', '29'])).
% 0.55/0.74  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['4', '21'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.55/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '27'])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ X1 @ X0)
% 0.55/0.74           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['32', '35'])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['25', '26'])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k1_tarski @ sk_B_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf(t17_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.55/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.55/0.74      inference('sup+', [status(thm)], ['40', '41'])).
% 0.55/0.74  thf('43', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.55/0.74      inference('sup+', [status(thm)], ['39', '42'])).
% 0.55/0.74  thf(t6_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.55/0.74       ( ( A ) = ( B ) ) ))).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X41 : $i, X42 : $i]:
% 0.55/0.74         (((X42) = (X41))
% 0.55/0.74          | ~ (r1_tarski @ (k1_tarski @ X42) @ (k1_tarski @ X41)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.55/0.74  thf('45', plain, (((sk_B_1) = (sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.74  thf('46', plain, (((sk_A) != (sk_B_1))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('47', plain, ($false),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
