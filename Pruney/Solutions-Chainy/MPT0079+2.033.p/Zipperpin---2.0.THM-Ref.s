%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L8Xo2H4TiN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 194 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  488 (1408 expanded)
%              Number of equality atoms :   56 ( 160 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference(demod,[status(thm)],['17','26'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('32',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('34',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['29','46'])).

thf('48',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','47'])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('50',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['29','46'])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['53','54','61'])).

thf('63',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['48','62'])).

thf('64',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L8Xo2H4TiN
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 278 iterations in 0.146s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(t72_xboole_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.45/0.63         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.45/0.63       ( ( C ) = ( B ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.45/0.63            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.45/0.63          ( ( C ) = ( B ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.45/0.63  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.63  thf('2', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.63  thf(d7_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf(t47_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.45/0.63           = (k4_xboole_0 @ X15 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.45/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf(t3_boole, axiom,
% 0.45/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.63  thf('7', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.63  thf('8', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.63  thf(t7_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf(t43_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.45/0.63       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.45/0.63          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.45/0.63          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '16'])).
% 0.45/0.63  thf('18', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.63  thf('20', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('22', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.45/0.63           = (k4_xboole_0 @ X15 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.45/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.63  thf('26', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain, ((r1_tarski @ sk_A @ sk_D)),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '26'])).
% 0.45/0.63  thf(t12_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.63  thf('29', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('32', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.45/0.63          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.63  thf('34', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('37', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.45/0.63           = (k4_xboole_0 @ X15 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.45/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.63  thf('40', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.63  thf('41', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.63  thf('44', plain, (((k2_xboole_0 @ sk_D @ sk_A) = (sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.63  thf('46', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.63  thf('47', plain, (((sk_D) = (sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['29', '46'])).
% 0.45/0.63  thf('48', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['8', '47'])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf('50', plain, (((sk_D) = (sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['29', '46'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf(t40_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.45/0.63           = (k4_xboole_0 @ X10 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 0.45/0.63         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.45/0.63           = (k4_xboole_0 @ X10 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.45/0.63  thf('55', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('57', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.45/0.63           = (k4_xboole_0 @ X15 @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.45/0.63  thf('60', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.63  thf('61', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.63  thf('62', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['53', '54', '61'])).
% 0.45/0.63  thf('63', plain, (((sk_B) = (sk_C))),
% 0.45/0.63      inference('sup+', [status(thm)], ['48', '62'])).
% 0.45/0.63  thf('64', plain, (((sk_C) != (sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('65', plain, ($false),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.49/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
