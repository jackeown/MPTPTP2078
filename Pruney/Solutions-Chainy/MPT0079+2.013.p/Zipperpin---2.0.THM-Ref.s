%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s4UGXIYOVa

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:58 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 295 expanded)
%              Number of leaves         :   20 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  504 (2210 expanded)
%              Number of equality atoms :   64 ( 266 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['15','24','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('29',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['26','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('48',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['26','45'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['4','46','47','48','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['26','45'])).

thf('61',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s4UGXIYOVa
% 0.13/0.36  % Computer   : n003.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:21:42 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 513 iterations in 0.193s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(t72_xboole_1, conjecture,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.44/0.66         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.44/0.66       ( ( C ) = ( B ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.44/0.66            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.44/0.66          ( ( C ) = ( B ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(commutativity_k2_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf(t40_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.44/0.66           = (k4_xboole_0 @ X12 @ X13))),
% 0.44/0.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.44/0.66         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.66  thf(t7_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.44/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf(t43_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.44/0.66       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.44/0.66          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.44/0.66          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.66  thf('11', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D)),
% 0.44/0.66      inference('sup-', [status(thm)], ['7', '10'])).
% 0.44/0.66  thf(t12_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X7 : $i, X8 : $i]:
% 0.44/0.66         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.44/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D) = (sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('16', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(d7_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('18', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf(t47_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.44/0.66           = (k4_xboole_0 @ X17 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.66      inference('sup+', [status(thm)], ['18', '21'])).
% 0.44/0.66  thf(t3_boole, axiom,
% 0.44/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.66  thf('23', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.66  thf('24', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.66  thf('26', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['15', '24', '25'])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('29', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.44/0.66          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.44/0.66  thf('31', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 0.44/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.66  thf('32', plain,
% 0.44/0.66      (![X7 : $i, X8 : $i]:
% 0.44/0.66         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.44/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.66  thf('33', plain,
% 0.44/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.66  thf('34', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.44/0.66  thf('36', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('37', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('38', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.66  thf('39', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.66  thf('41', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.66  thf('42', plain,
% 0.44/0.66      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.44/0.66      inference('sup+', [status(thm)], ['40', '41'])).
% 0.44/0.66  thf('43', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.66  thf('44', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.44/0.66      inference('demod', [status(thm)], ['42', '43'])).
% 0.44/0.66  thf('45', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['35', '44'])).
% 0.44/0.66  thf('46', plain, (((sk_D) = (sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['26', '45'])).
% 0.44/0.66  thf('47', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.44/0.66           = (k4_xboole_0 @ X12 @ X13))),
% 0.44/0.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.44/0.66  thf('48', plain, (((sk_D) = (sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['26', '45'])).
% 0.44/0.66  thf('49', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.66  thf('50', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.44/0.66           = (k4_xboole_0 @ X17 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.66  thf('51', plain,
% 0.44/0.66      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['49', '50'])).
% 0.44/0.66  thf('52', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.66  thf('53', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['51', '52'])).
% 0.44/0.66  thf('54', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.44/0.66      inference('demod', [status(thm)], ['4', '46', '47', '48', '53'])).
% 0.44/0.66  thf('55', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.66  thf('56', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.44/0.66           = (k4_xboole_0 @ X17 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.44/0.66      inference('sup+', [status(thm)], ['55', '56'])).
% 0.44/0.66  thf('58', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.66  thf('59', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.44/0.66  thf('60', plain, (((sk_D) = (sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['26', '45'])).
% 0.44/0.66  thf('61', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['59', '60'])).
% 0.44/0.66  thf('62', plain, (((sk_B) = (sk_C))),
% 0.44/0.66      inference('sup+', [status(thm)], ['54', '61'])).
% 0.44/0.66  thf('63', plain, (((sk_C) != (sk_B))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('64', plain, ($false),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
