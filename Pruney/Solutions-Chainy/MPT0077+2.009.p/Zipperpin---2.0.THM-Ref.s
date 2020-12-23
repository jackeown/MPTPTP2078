%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h5NloQk24D

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 219 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  607 (2206 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','25','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( ( k4_xboole_0 @ X8 @ X7 )
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('50',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','25','49'])).

thf('51',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['27','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h5NloQk24D
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 556 iterations in 0.278s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(t70_xboole_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.46/0.70            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.46/0.70       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.46/0.70            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.46/0.70               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.46/0.70          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.46/0.70               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.46/0.70        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.46/0.70         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.46/0.70       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.46/0.70        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf(symmetry_r1_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf(t7_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.70  thf(t63_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.46/0.70       ( r1_xboole_0 @ A @ C ) ))).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X18 @ X19)
% 0.46/0.70          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.46/0.70          | (r1_xboole_0 @ X18 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X1 @ X2)
% 0.46/0.70          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_B @ sk_A))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.46/0.70       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X18 @ X19)
% 0.46/0.70          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.46/0.70          | (r1_xboole_0 @ X18 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X0 @ X2)
% 0.46/0.70          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_C @ sk_A))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['15', '20'])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.46/0.70       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.70  thf('26', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 0.46/0.70  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.46/0.70        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.70      inference('split', [status(esa)], ['28'])).
% 0.46/0.70  thf(d7_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.70       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.46/0.70       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('split', [status(esa)], ['28'])).
% 0.46/0.70  thf('33', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '32'])).
% 0.46/0.70  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.70  thf(t46_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf(t41_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.46/0.70           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf(t32_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.46/0.70       ( ( A ) = ( B ) ) ))).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         (((X8) = (X7)) | ((k4_xboole_0 @ X8 @ X7) != (k4_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) != (k1_xboole_0))
% 0.46/0.70          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.70  thf(t48_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.70           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 0.46/0.70          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70         | ((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '46'])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.46/0.70       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf('50', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '49'])).
% 0.46/0.70  thf('51', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.46/0.70           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.70           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.70           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.46/0.70           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['51', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.70           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ sk_A @ X0)
% 0.46/0.70           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X2 : $i, X4 : $i]:
% 0.46/0.70         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.46/0.70          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['34', '59'])).
% 0.46/0.70  thf('61', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.70  thf('62', plain, ($false), inference('demod', [status(thm)], ['27', '61'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
