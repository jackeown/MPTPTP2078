%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zdr1MnjEj5

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 264 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  641 (2553 expanded)
%              Number of equality atoms :   39 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X48 @ X49 )
      | ( r1_tarski @ ( k2_xboole_0 @ X48 @ X50 ) @ ( k2_xboole_0 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r1_xboole_0 @ X43 @ X44 )
      | ~ ( r1_tarski @ X43 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ~ ( r1_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['31','32','48','58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['29','60'])).

thf('62',plain,
    ( $false
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['1','61'])).

thf('63',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','32','48','58'])).

thf('64',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zdr1MnjEj5
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 383 iterations in 0.238s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(t70_xboole_1, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.51/0.74            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.51/0.74       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.51/0.74            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.74        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.51/0.74               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.51/0.74          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.51/0.74               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 0.51/0.74        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.51/0.74        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.51/0.74        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.51/0.74      inference('split', [status(esa)], ['2'])).
% 0.51/0.74  thf(commutativity_k2_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('4', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.51/0.74  thf('5', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.51/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.51/0.74  thf(t9_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( r1_tarski @ A @ B ) =>
% 0.51/0.74       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.51/0.74         (~ (r1_tarski @ X48 @ X49)
% 0.51/0.74          | (r1_tarski @ (k2_xboole_0 @ X48 @ X50) @ (k2_xboole_0 @ X49 @ X50)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.51/0.74          (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.74  thf(t40_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 0.51/0.74           = (k4_xboole_0 @ X23 @ X24))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf(t3_boole, axiom,
% 0.51/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.74  thf('9', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.51/0.74  thf('11', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('demod', [status(thm)], ['7', '14'])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '15'])).
% 0.51/0.74  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf(t46_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X28 @ (k2_xboole_0 @ X28 @ X29)) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.51/0.74  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['17', '18'])).
% 0.51/0.74  thf(t39_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.51/0.74           = (k2_xboole_0 @ X19 @ X20))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['19', '20'])).
% 0.51/0.74  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('23', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('demod', [status(thm)], ['7', '14'])).
% 0.51/0.74  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.51/0.74      inference('sup+', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf(t64_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.51/0.74         ( r1_xboole_0 @ B @ D ) ) =>
% 0.51/0.74       ( r1_xboole_0 @ A @ C ) ))).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ X43 @ X44)
% 0.51/0.74          | ~ (r1_tarski @ X43 @ X45)
% 0.51/0.74          | ~ (r1_tarski @ X44 @ X46)
% 0.51/0.74          | ~ (r1_xboole_0 @ X45 @ X46))),
% 0.51/0.74      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.51/0.74  thf('27', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (r1_xboole_0 @ X0 @ X1)
% 0.51/0.74          | ~ (r1_tarski @ X2 @ X1)
% 0.51/0.74          | (r1_xboole_0 @ X0 @ X2))),
% 0.51/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ X2 @ X1)
% 0.51/0.74          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['16', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['3', '28'])).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.51/0.74        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.51/0.74       ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('split', [status(esa)], ['30'])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (~ ((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.51/0.74       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['30'])).
% 0.51/0.74  thf(d7_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.51/0.74       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('split', [status(esa)], ['2'])).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf(t23_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.51/0.74       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.51/0.74           = (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ 
% 0.51/0.74              (k3_xboole_0 @ X11 @ X13)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.51/0.74            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['38', '39'])).
% 0.51/0.74  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.51/0.74            = (k3_xboole_0 @ sk_A @ X0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (![X2 : $i, X4 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.74  thf('44', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.51/0.74           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      (((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.74         | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['35', '44'])).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.51/0.74         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.51/0.74       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.51/0.74            = (k3_xboole_0 @ sk_A @ X0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.51/0.74      inference('split', [status(esa)], ['2'])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.51/0.74  thf('53', plain,
% 0.51/0.74      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.51/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['49', '52'])).
% 0.51/0.74  thf('54', plain,
% 0.51/0.74      (![X2 : $i, X4 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C_1)))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.51/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 0.51/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.51/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['55'])).
% 0.51/0.74  thf('57', plain,
% 0.51/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.51/0.74       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.51/0.74       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.51/0.74  thf('59', plain,
% 0.51/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.51/0.74       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('split', [status(esa)], ['2'])).
% 0.51/0.74  thf('60', plain, (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('sat_resolution*', [status(thm)],
% 0.51/0.74                ['31', '32', '48', '58', '59'])).
% 0.51/0.74  thf('61', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.51/0.74      inference('simpl_trail', [status(thm)], ['29', '60'])).
% 0.51/0.74  thf('62', plain, (($false) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['1', '61'])).
% 0.51/0.74  thf('63', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.51/0.74      inference('sat_resolution*', [status(thm)], ['31', '32', '48', '58'])).
% 0.51/0.74  thf('64', plain, ($false),
% 0.51/0.74      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.58/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
