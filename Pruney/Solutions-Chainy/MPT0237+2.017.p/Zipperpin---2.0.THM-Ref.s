%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZPVPljaXv8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 107 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  444 ( 739 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X57 ) @ ( k1_tarski @ X58 ) )
        = ( k2_tarski @ X57 @ X58 ) )
      | ( X57 = X58 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('10',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['12','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('36',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['12','14'])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','15','40','41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZPVPljaXv8
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 304 iterations in 0.129s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(t32_zfmisc_1, conjecture,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.36/0.59       ( k2_tarski @ A @ B ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]:
% 0.36/0.59        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.36/0.59          ( k2_tarski @ A @ B ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.36/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(l51_zfmisc_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X55 : $i, X56 : $i]:
% 0.36/0.59         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.36/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf(t29_zfmisc_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( A ) != ( B ) ) =>
% 0.36/0.59       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.59         ( k2_tarski @ A @ B ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X57 : $i, X58 : $i]:
% 0.36/0.59         (((k5_xboole_0 @ (k1_tarski @ X57) @ (k1_tarski @ X58))
% 0.36/0.59            = (k2_tarski @ X57 @ X58))
% 0.36/0.59          | ((X57) = (X58)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.36/0.59  thf(l27_zfmisc_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X53 : $i, X54 : $i]:
% 0.36/0.59         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 0.36/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.36/0.59  thf(t83_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i]:
% 0.36/0.59         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((r2_hidden @ X1 @ X0)
% 0.36/0.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.59  thf(t98_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X18 @ X19)
% 0.36/0.59           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.36/0.59            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.36/0.59          | (r2_hidden @ X0 @ X1))),
% 0.36/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.59          != (k2_tarski @ sk_A @ sk_B))
% 0.36/0.59        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.36/0.59        | ((sk_A) = (sk_B))
% 0.36/0.59        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['3', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.59  thf(d1_tarski, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X23 @ X22)
% 0.36/0.59          | ((X23) = (X20))
% 0.36/0.59          | ((X22) != (k1_tarski @ X20)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X20 : $i, X23 : $i]:
% 0.36/0.59         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.59  thf('15', plain, (((sk_A) = (sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['12', '14'])).
% 0.36/0.59  thf(t69_enumset1, axiom,
% 0.36/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.36/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X55 : $i, X56 : $i]:
% 0.36/0.59         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.36/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(t7_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.36/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_tarski @ X0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf(t28_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i]:
% 0.36/0.59         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.36/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf(t17_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.36/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.59  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.59  thf(l32_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X2 : $i, X4 : $i]:
% 0.36/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.59  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X18 @ X19)
% 0.36/0.59           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.59  thf('30', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i]:
% 0.36/0.59         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.36/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['29', '32'])).
% 0.36/0.59  thf(t100_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.36/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.59  thf('36', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.36/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i]:
% 0.36/0.59         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.59  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['35', '38'])).
% 0.36/0.59  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['28', '39'])).
% 0.36/0.59  thf('41', plain, (((sk_A) = (sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['12', '14'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.36/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.59  thf('43', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '15', '40', '41', '42'])).
% 0.36/0.59  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
