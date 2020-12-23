%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V4boWSsggu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 123 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  528 ( 863 expanded)
%              Number of equality atoms :   43 (  73 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','21'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','42'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V4boWSsggu
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 133 iterations in 0.060s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(t46_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.49       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.49          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.22/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l1_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X39 : $i, X41 : $i]:
% 0.22/0.49         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 0.22/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.49  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t28_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X20 : $i, X21 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X17 @ X18)
% 0.22/0.49           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.22/0.49         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('9', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.22/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X20 : $i, X21 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.49  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X17 @ X18)
% 0.22/0.49           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X17 @ X18)
% 0.22/0.49           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf(t1_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.22/0.49       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         ((r2_hidden @ X10 @ X11)
% 0.22/0.49          | (r2_hidden @ X10 @ X12)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.49          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49          | (r2_hidden @ X2 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X17 @ X18)
% 0.22/0.49           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ X12)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf(d4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.49           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.22/0.49          | (r2_hidden @ X8 @ X5)
% 0.22/0.49          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.22/0.49         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['19', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((r2_hidden @ X2 @ X1) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['16', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '23'])).
% 0.22/0.49  thf('25', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['19', '21'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.49          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.49          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('clc', [status(thm)], ['24', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('34', plain, (![X24 : $i]: ((k4_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ X12)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['32', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X14 : $i, X16 : $i]:
% 0.22/0.49         (((X14) = (X16))
% 0.22/0.49          | ~ (r1_tarski @ X16 @ X14)
% 0.22/0.49          | ~ (r1_tarski @ X14 @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '41'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '42'])).
% 0.22/0.49  thf(t39_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X22 : $i, X23 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.22/0.49           = (k2_xboole_0 @ X22 @ X23))),
% 0.22/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.22/0.49         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['43', '44'])).
% 0.22/0.49  thf(t1_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('46', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.49  thf('47', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.49  thf('48', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(commutativity_k2_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.49  thf(l51_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X42 : $i, X43 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['49', '50'])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (![X42 : $i, X43 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '53'])).
% 0.22/0.49  thf('55', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['47', '54'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
