%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l32miyokFd

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:02 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 116 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 ( 926 expanded)
%              Number of equality atoms :   64 ( 118 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
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
    ! [X59: $i,X60: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X59 ) @ ( k1_tarski @ X60 ) )
        = ( k2_tarski @ X59 @ X60 ) )
      | ( X59 = X60 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X56 ) )
      | ( X55 = X56 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

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
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
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

thf('21',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X52 ) )
      | ( X51
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('22',plain,(
    ! [X49: $i,X52: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X52 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf('39',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','19','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l32miyokFd
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.75/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/1.00  % Solved by: fo/fo7.sh
% 0.75/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/1.00  % done 1026 iterations in 0.538s
% 0.75/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/1.00  % SZS output start Refutation
% 0.75/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.75/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/1.00  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/1.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.75/1.00  thf(t32_zfmisc_1, conjecture,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.75/1.00       ( k2_tarski @ A @ B ) ))).
% 0.75/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.75/1.00    (~( ![A:$i,B:$i]:
% 0.75/1.00        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.75/1.00          ( k2_tarski @ A @ B ) ) )),
% 0.75/1.00    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.75/1.00  thf('0', plain,
% 0.75/1.00      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.75/1.00         != (k2_tarski @ sk_A @ sk_B))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(l51_zfmisc_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/1.00  thf('1', plain,
% 0.75/1.00      (![X53 : $i, X54 : $i]:
% 0.75/1.00         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.75/1.00      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/1.00  thf('2', plain,
% 0.75/1.00      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/1.00         != (k2_tarski @ sk_A @ sk_B))),
% 0.75/1.00      inference('demod', [status(thm)], ['0', '1'])).
% 0.75/1.00  thf(t29_zfmisc_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( ( A ) != ( B ) ) =>
% 0.75/1.00       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.75/1.00         ( k2_tarski @ A @ B ) ) ))).
% 0.75/1.00  thf('3', plain,
% 0.75/1.00      (![X59 : $i, X60 : $i]:
% 0.75/1.00         (((k5_xboole_0 @ (k1_tarski @ X59) @ (k1_tarski @ X60))
% 0.75/1.00            = (k2_tarski @ X59 @ X60))
% 0.75/1.00          | ((X59) = (X60)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.75/1.00  thf(t17_zfmisc_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( ( A ) != ( B ) ) =>
% 0.75/1.00       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.75/1.00  thf('4', plain,
% 0.75/1.00      (![X55 : $i, X56 : $i]:
% 0.75/1.00         ((r1_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X56))
% 0.75/1.00          | ((X55) = (X56)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.75/1.00  thf(t83_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/1.00  thf('5', plain,
% 0.75/1.00      (![X13 : $i, X14 : $i]:
% 0.75/1.00         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.75/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/1.00  thf('6', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         (((X1) = (X0))
% 0.75/1.00          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.75/1.00              = (k1_tarski @ X1)))),
% 0.75/1.00      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/1.00  thf(commutativity_k3_xboole_0, axiom,
% 0.75/1.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/1.00  thf('7', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/1.00  thf(t94_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( k2_xboole_0 @ A @ B ) =
% 0.75/1.00       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/1.00  thf('8', plain,
% 0.75/1.00      (![X19 : $i, X20 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ X19 @ X20)
% 0.75/1.00           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.75/1.00              (k3_xboole_0 @ X19 @ X20)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.75/1.00  thf(t91_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/1.00       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/1.00  thf('9', plain,
% 0.75/1.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/1.00         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.75/1.00           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/1.00  thf('10', plain,
% 0.75/1.00      (![X19 : $i, X20 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ X19 @ X20)
% 0.75/1.00           = (k5_xboole_0 @ X19 @ 
% 0.75/1.00              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.75/1.00      inference('demod', [status(thm)], ['8', '9'])).
% 0.75/1.00  thf('11', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ X0 @ X1)
% 0.75/1.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.75/1.00      inference('sup+', [status(thm)], ['7', '10'])).
% 0.75/1.00  thf(t100_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/1.00  thf('12', plain,
% 0.75/1.00      (![X5 : $i, X6 : $i]:
% 0.75/1.00         ((k4_xboole_0 @ X5 @ X6)
% 0.75/1.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/1.00  thf('13', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ X0 @ X1)
% 0.75/1.00           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/1.00      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/1.00  thf('14', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.75/1.00            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.75/1.00          | ((X0) = (X1)))),
% 0.75/1.00      inference('sup+', [status(thm)], ['6', '13'])).
% 0.75/1.00  thf('15', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.75/1.00            = (k2_tarski @ X1 @ X0))
% 0.75/1.00          | ((X1) = (X0))
% 0.75/1.00          | ((X0) = (X1)))),
% 0.75/1.00      inference('sup+', [status(thm)], ['3', '14'])).
% 0.75/1.00  thf('16', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         (((X1) = (X0))
% 0.75/1.00          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.75/1.00              = (k2_tarski @ X1 @ X0)))),
% 0.75/1.00      inference('simplify', [status(thm)], ['15'])).
% 0.75/1.00  thf('17', plain,
% 0.75/1.00      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/1.00         != (k2_tarski @ sk_A @ sk_B))),
% 0.75/1.00      inference('demod', [status(thm)], ['0', '1'])).
% 0.75/1.00  thf('18', plain,
% 0.75/1.00      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.75/1.00        | ((sk_A) = (sk_B)))),
% 0.75/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.75/1.00  thf('19', plain, (((sk_A) = (sk_B))),
% 0.75/1.00      inference('simplify', [status(thm)], ['18'])).
% 0.75/1.00  thf(t69_enumset1, axiom,
% 0.75/1.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/1.00  thf('20', plain,
% 0.75/1.00      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.75/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/1.00  thf(l45_zfmisc_1, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.75/1.00       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.75/1.00            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.75/1.00  thf('21', plain,
% 0.75/1.00      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.75/1.00         ((r1_tarski @ X51 @ (k2_tarski @ X49 @ X52))
% 0.75/1.00          | ((X51) != (k1_tarski @ X49)))),
% 0.75/1.00      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.75/1.00  thf('22', plain,
% 0.75/1.00      (![X49 : $i, X52 : $i]:
% 0.75/1.00         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X52))),
% 0.75/1.00      inference('simplify', [status(thm)], ['21'])).
% 0.75/1.00  thf('23', plain,
% 0.75/1.00      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.75/1.00      inference('sup+', [status(thm)], ['20', '22'])).
% 0.75/1.00  thf(l32_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/1.00  thf('24', plain,
% 0.75/1.00      (![X2 : $i, X4 : $i]:
% 0.75/1.00         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.75/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/1.00  thf('25', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.75/1.00      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/1.00  thf('26', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ X0 @ X1)
% 0.75/1.00           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/1.00      inference('demod', [status(thm)], ['11', '12'])).
% 0.75/1.00  thf('27', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.75/1.00           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.75/1.00      inference('sup+', [status(thm)], ['25', '26'])).
% 0.75/1.00  thf('28', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/1.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/1.00  thf('29', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.75/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/1.00  thf(t28_xboole_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/1.00  thf('30', plain,
% 0.75/1.00      (![X9 : $i, X10 : $i]:
% 0.75/1.00         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.75/1.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/1.00  thf('31', plain,
% 0.75/1.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/1.00  thf('32', plain,
% 0.75/1.00      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/1.00      inference('sup+', [status(thm)], ['28', '31'])).
% 0.75/1.00  thf('33', plain,
% 0.75/1.00      (![X5 : $i, X6 : $i]:
% 0.75/1.00         ((k4_xboole_0 @ X5 @ X6)
% 0.75/1.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.75/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/1.00  thf('34', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/1.00      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/1.00  thf(t3_boole, axiom,
% 0.75/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/1.00  thf('35', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.75/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/1.00  thf('36', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/1.00      inference('demod', [status(thm)], ['34', '35'])).
% 0.75/1.00  thf('37', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.75/1.00           = (k1_tarski @ X0))),
% 0.75/1.00      inference('demod', [status(thm)], ['27', '36'])).
% 0.75/1.00  thf('38', plain, (((sk_A) = (sk_B))),
% 0.75/1.00      inference('simplify', [status(thm)], ['18'])).
% 0.75/1.00  thf('39', plain,
% 0.75/1.00      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.75/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/1.00  thf('40', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.75/1.00      inference('demod', [status(thm)], ['2', '19', '37', '38', '39'])).
% 0.75/1.00  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.75/1.00  
% 0.75/1.00  % SZS output end Refutation
% 0.75/1.00  
% 0.75/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
