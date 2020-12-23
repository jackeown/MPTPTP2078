%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0hZNDE48nz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:14 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 184 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  608 (1413 expanded)
%              Number of equality atoms :   66 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ( ( k4_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('32',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ~ ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('37',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('57',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','34','56'])).

thf('58',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['36','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0hZNDE48nz
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.54  % Solved by: fo/fo7.sh
% 0.38/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.54  % done 209 iterations in 0.087s
% 0.38/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.54  % SZS output start Refutation
% 0.38/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.54  thf(t67_zfmisc_1, conjecture,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.54       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.38/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.54    (~( ![A:$i,B:$i]:
% 0.38/0.54        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.54          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.38/0.54    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.38/0.54  thf('0', plain,
% 0.38/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.38/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('1', plain,
% 0.38/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('2', plain,
% 0.38/0.54      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.38/0.54       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('3', plain,
% 0.38/0.54      (((r2_hidden @ sk_A @ sk_B_1)
% 0.38/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('4', plain,
% 0.38/0.54      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.38/0.54      inference('split', [status(esa)], ['3'])).
% 0.38/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.54  thf('5', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.38/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.54  thf(t28_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.54  thf('6', plain,
% 0.38/0.54      (![X12 : $i, X13 : $i]:
% 0.38/0.54         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.54  thf('7', plain,
% 0.38/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.54  thf('8', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('9', plain,
% 0.38/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.54  thf(t100_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.54  thf('10', plain,
% 0.38/0.54      (![X10 : $i, X11 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X10 @ X11)
% 0.38/0.54           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.54  thf('11', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.54  thf(t5_boole, axiom,
% 0.38/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.54  thf('12', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.38/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.54  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.54  thf(t48_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.54  thf('14', plain,
% 0.38/0.54      (![X15 : $i, X16 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.38/0.54           = (k3_xboole_0 @ X15 @ X16))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.54  thf('15', plain,
% 0.38/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.54  thf('16', plain,
% 0.38/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.54  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.54  thf('18', plain,
% 0.38/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('19', plain,
% 0.38/0.54      (![X15 : $i, X16 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.38/0.54           = (k3_xboole_0 @ X15 @ X16))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.54  thf('20', plain,
% 0.38/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.38/0.54          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.54  thf('21', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('22', plain,
% 0.38/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.38/0.54          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.54  thf('23', plain,
% 0.38/0.54      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('sup+', [status(thm)], ['17', '22'])).
% 0.38/0.54  thf('24', plain,
% 0.38/0.54      (![X10 : $i, X11 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X10 @ X11)
% 0.38/0.54           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.54  thf('25', plain,
% 0.38/0.54      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.38/0.54          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.38/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.38/0.54  thf('26', plain,
% 0.38/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.54  thf('27', plain,
% 0.38/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.54  thf('28', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.38/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.54  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.54  thf('30', plain,
% 0.38/0.54      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1)))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.38/0.54  thf(t65_zfmisc_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.38/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.38/0.54  thf('31', plain,
% 0.38/0.54      (![X51 : $i, X52 : $i]:
% 0.38/0.54         (~ (r2_hidden @ X51 @ X52)
% 0.38/0.54          | ((k4_xboole_0 @ X52 @ (k1_tarski @ X51)) != (X52)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.54  thf('32', plain,
% 0.38/0.54      (((((sk_B_1) != (sk_B_1)) | ~ (r2_hidden @ sk_A @ sk_B_1)))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.54  thf('33', plain,
% 0.38/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 0.38/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.54  thf('34', plain,
% 0.38/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.38/0.54       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.38/0.54      inference('sup-', [status(thm)], ['4', '33'])).
% 0.38/0.54  thf('35', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.38/0.54      inference('sat_resolution*', [status(thm)], ['2', '34'])).
% 0.38/0.54  thf('36', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.38/0.54      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.38/0.54  thf(l27_zfmisc_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.38/0.54  thf('37', plain,
% 0.38/0.54      (![X49 : $i, X50 : $i]:
% 0.38/0.54         ((r1_xboole_0 @ (k1_tarski @ X49) @ X50) | (r2_hidden @ X49 @ X50))),
% 0.38/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.38/0.54  thf(t4_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.54  thf('38', plain,
% 0.38/0.54      (![X5 : $i, X6 : $i]:
% 0.38/0.54         ((r1_xboole_0 @ X5 @ X6)
% 0.38/0.54          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.54  thf('39', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('40', plain,
% 0.38/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.38/0.54         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.38/0.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.54  thf('41', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.54          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.54  thf('42', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('sup-', [status(thm)], ['38', '41'])).
% 0.38/0.54  thf('43', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['37', '42'])).
% 0.38/0.54  thf(t7_xboole_0, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.54  thf('44', plain,
% 0.38/0.54      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.38/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.54  thf('45', plain,
% 0.38/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.38/0.54         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.38/0.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.54  thf('46', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.54  thf('47', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((r2_hidden @ X0 @ X1)
% 0.38/0.54          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['43', '46'])).
% 0.38/0.54  thf('48', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('49', plain,
% 0.38/0.54      (![X10 : $i, X11 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X10 @ X11)
% 0.38/0.54           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.54  thf('50', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.38/0.54  thf('51', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.38/0.54            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.38/0.54          | (r2_hidden @ X0 @ X1))),
% 0.38/0.54      inference('sup+', [status(thm)], ['47', '50'])).
% 0.38/0.54  thf('52', plain,
% 0.38/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.54  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.54  thf('54', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.38/0.54          | (r2_hidden @ X0 @ X1))),
% 0.38/0.54      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.38/0.54  thf('55', plain,
% 0.38/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.38/0.54         <= (~
% 0.38/0.54             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.38/0.54      inference('split', [status(esa)], ['3'])).
% 0.38/0.54  thf('56', plain,
% 0.38/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.38/0.54       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.38/0.54      inference('split', [status(esa)], ['3'])).
% 0.38/0.54  thf('57', plain,
% 0.38/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.38/0.54      inference('sat_resolution*', [status(thm)], ['2', '34', '56'])).
% 0.38/0.54  thf('58', plain,
% 0.38/0.54      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.38/0.54      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.38/0.54  thf('59', plain,
% 0.38/0.54      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.38/0.54        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.38/0.54      inference('sup-', [status(thm)], ['54', '58'])).
% 0.38/0.54  thf('60', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.38/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.38/0.54  thf('61', plain, ($false), inference('demod', [status(thm)], ['36', '60'])).
% 0.38/0.54  
% 0.38/0.54  % SZS output end Refutation
% 0.38/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
