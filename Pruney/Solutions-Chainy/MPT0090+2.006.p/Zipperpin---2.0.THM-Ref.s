%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9YTOV9biba

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 188 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  533 (1452 expanded)
%              Number of equality atoms :   59 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_A )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('40',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['11','40','41'])).

thf('43',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('58',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['11','40'])).

thf('59',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9YTOV9biba
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 152 iterations in 0.035s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(t83_xboole_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(d7_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(t48_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.48           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.48           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.48           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.48          = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.21/0.48         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf(t3_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('8', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.21/0.48         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.21/0.48       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('12', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.48           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X2 : $i, X4 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf(t3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X9 @ X7)
% 0.21/0.48          | ~ (r2_hidden @ X9 @ X10)
% 0.21/0.48          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.48           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X2 : $i, X4 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))
% 0.21/0.48         | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((((k3_xboole_0 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.48         | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.21/0.48       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('42', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['11', '40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['9', '42'])).
% 0.21/0.48  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.48  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.48           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.48           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('52', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('53', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.48  thf(t49_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.48       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.21/0.48           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.48           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['43', '55'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.21/0.48         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('58', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['11', '40'])).
% 0.21/0.48  thf('59', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.21/0.48  thf('60', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
