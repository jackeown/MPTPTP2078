%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JPm75ksh47

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 128 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  496 ( 852 expanded)
%              Number of equality atoms :   59 ( 103 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    r2_hidden @ sk_C @ sk_B ),
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
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','29','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','47'])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('55',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JPm75ksh47
% 0.14/0.37  % Computer   : n024.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:16:21 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 251 iterations in 0.113s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(t48_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.37/0.61       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.37/0.61          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.37/0.61  thf('0', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t38_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.37/0.61          | ~ (r2_hidden @ X30 @ X31)
% 0.37/0.61          | ~ (r2_hidden @ X28 @ X31))),
% 0.37/0.61      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C @ sk_A) @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf(commutativity_k2_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i]:
% 0.37/0.61         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.61  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.37/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf(t28_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.37/0.61         = (k2_tarski @ sk_A @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.37/0.61         = (k2_tarski @ sk_A @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf(t100_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.37/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_A @ sk_C)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['10', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i]:
% 0.37/0.61         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.61  thf(l51_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.37/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.37/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf(t1_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('20', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.61  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf(t40_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.37/0.61           = (k4_xboole_0 @ X13 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.37/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.61  thf('30', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.61           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf(t39_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.37/0.61           = (k2_xboole_0 @ X11 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.61  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.61  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['39', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '45'])).
% 0.37/0.61  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['23', '29', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['14', '47'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.37/0.61           = (k2_xboole_0 @ X11 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.37/0.61         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('51', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) != (sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.61  thf('56', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
