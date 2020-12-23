%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfcCGWoeYS

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:14 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 153 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  556 (1133 expanded)
%              Number of equality atoms :   64 ( 171 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('1',plain,(
    ! [X56: $i] :
      ( ~ ( r2_hidden @ X56 @ sk_A )
      | ( X56 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) )
    = ( k2_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) )
    = ( k2_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    = ( k2_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X56: $i] :
      ( ~ ( r2_hidden @ X56 @ sk_A )
      | ( X56 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X48 ) @ X50 )
      | ~ ( r2_hidden @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    | ( ( k2_tarski @ sk_B_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('34',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54 != X53 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ ( k1_tarski @ X53 ) )
       != ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('35',plain,(
    ! [X53: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X53 ) )
     != ( k1_tarski @ X53 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('40',plain,(
    ! [X53: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X53 ) ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['32','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['19','51'])).

thf('53',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    sk_A
 != ( k2_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfcCGWoeYS
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 874 iterations in 0.274s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.73  thf(t7_xboole_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      (![X11 : $i]:
% 0.54/0.73         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.54/0.73  thf(t41_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i]:
% 0.54/0.73        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X56 : $i]: (~ (r2_hidden @ X56 @ sk_A) | ((X56) = (sk_B_1)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('2', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('4', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X11 : $i]:
% 0.54/0.73         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.54/0.73  thf('6', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('8', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.54/0.73  thf(l31_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.54/0.73       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X51 : $i, X52 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.54/0.73          | ~ (r2_hidden @ X51 @ X52))),
% 0.54/0.73      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf(t69_enumset1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))
% 0.54/0.73         = (k2_tarski @ sk_B_1 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.54/0.73  thf(t100_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X12 @ X13)
% 0.54/0.73           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))
% 0.54/0.73         = (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf(t48_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.54/0.73           = (k3_xboole_0 @ X16 @ X17))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ 
% 0.54/0.73         (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))
% 0.54/0.73         = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))
% 0.54/0.73         = (k2_tarski @ sk_B_1 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ 
% 0.54/0.73         (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))
% 0.54/0.73         = (k2_tarski @ sk_B_1 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf(t3_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.54/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.73            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X56 : $i]: (~ (r2_hidden @ X56 @ sk_A) | ((X56) = (sk_B_1)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ sk_B_1 @ X0)
% 0.54/0.73          | (r1_xboole_0 @ sk_A @ X0)
% 0.54/0.73          | (r1_xboole_0 @ sk_A @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ sk_B_1 @ X0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['24'])).
% 0.54/0.73  thf(l1_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X48 : $i, X50 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_tarski @ X48) @ X50) | ~ (r2_hidden @ X48 @ X50))),
% 0.54/0.73      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ sk_A @ X0) | (r1_tarski @ (k1_tarski @ sk_B_1) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ sk_A @ X0)
% 0.54/0.73          | (r1_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1) @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))
% 0.54/0.73         = (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf(t38_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.54/0.73       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i]:
% 0.54/0.73         (((X14) = (k1_xboole_0))
% 0.54/0.73          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      ((~ (r1_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1) @ 
% 0.54/0.73           (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))
% 0.54/0.73        | ((k2_tarski @ sk_B_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf(t20_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.54/0.73         ( k1_tarski @ A ) ) <=>
% 0.54/0.73       ( ( A ) != ( B ) ) ))).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      (![X53 : $i, X54 : $i]:
% 0.54/0.73         (((X54) != (X53))
% 0.54/0.73          | ((k4_xboole_0 @ (k1_tarski @ X54) @ (k1_tarski @ X53))
% 0.54/0.73              != (k1_tarski @ X54)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (![X53 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X53))
% 0.54/0.73           != (k1_tarski @ X53))),
% 0.54/0.73      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.54/0.73  thf('36', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X12 @ X13)
% 0.54/0.73           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('38', plain,
% 0.54/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['36', '37'])).
% 0.54/0.73  thf(t92_xboole_1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.73  thf('39', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.73  thf('40', plain, (![X53 : $i]: ((k1_xboole_0) != (k1_tarski @ X53))),
% 0.54/0.73      inference('demod', [status(thm)], ['35', '38', '39'])).
% 0.54/0.73  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['33', '40'])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      (~ (r1_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1) @ 
% 0.54/0.73          (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.54/0.73      inference('clc', [status(thm)], ['32', '41'])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      ((r1_xboole_0 @ sk_A @ 
% 0.54/0.73        (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['29', '42'])).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X11 : $i]:
% 0.54/0.73         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.54/0.73  thf(t4_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.73            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.54/0.73          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ 
% 0.54/0.73         (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['43', '46'])).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X12 @ X13)
% 0.54/0.73           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ 
% 0.54/0.73         (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1)))
% 0.54/0.73         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['47', '48'])).
% 0.54/0.73  thf(t5_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.73  thf('50', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.54/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.73  thf('51', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ 
% 0.54/0.73         (k5_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_B_1))) = (sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.73  thf('52', plain, (((k2_tarski @ sk_B_1 @ sk_B_1) = (sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['19', '51'])).
% 0.54/0.73  thf('53', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('55', plain, (((sk_A) != (k2_tarski @ sk_B_1 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.54/0.73  thf('56', plain, ($false),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
