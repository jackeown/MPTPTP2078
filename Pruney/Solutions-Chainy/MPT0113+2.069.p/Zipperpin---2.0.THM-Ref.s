%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44uDR8SeAu

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:37 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 338 expanded)
%              Number of leaves         :   23 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  559 (2429 expanded)
%              Number of equality atoms :   57 ( 211 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','39'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','64'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k3_xboole_0 @ X7 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['54','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44uDR8SeAu
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 772 iterations in 0.362s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.82  thf(t106_xboole_1, conjecture,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.82       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.82        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.82          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(l32_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X10 : $i, X12 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.58/0.82          | ~ (r1_tarski @ X10 @ X12))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf(t52_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.58/0.82       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.58/0.82           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.58/0.82              (k3_xboole_0 @ X23 @ X25)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.58/0.82  thf(d3_tarski, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X4 : $i, X6 : $i]:
% 0.58/0.82         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf(d1_xboole_0, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      (![X10 : $i, X12 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.58/0.82          | ~ (r1_tarski @ X10 @ X12))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ X1) | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.82  thf(t4_boole, axiom,
% 0.58/0.82    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t4_boole])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]:
% 0.58/0.82         ((r1_tarski @ X10 @ X11)
% 0.58/0.82          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.82  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.82  thf(t45_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) =>
% 0.58/0.82       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (![X16 : $i, X17 : $i]:
% 0.58/0.82         (((X17) = (k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))
% 0.58/0.82          | ~ (r1_tarski @ X16 @ X17))),
% 0.58/0.82      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((X0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.58/0.82          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['10', '16'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t4_boole])).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['18', '19'])).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (![X4 : $i, X6 : $i]:
% 0.58/0.82         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('23', plain,
% 0.58/0.82      (![X4 : $i, X6 : $i]:
% 0.58/0.82         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.82  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.82      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (![X10 : $i, X12 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.58/0.82          | ~ (r1_tarski @ X10 @ X12))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.82  thf(t48_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.58/0.82           = (k3_xboole_0 @ X20 @ X21))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('29', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('32', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.82  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.58/0.82           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.58/0.82              (k3_xboole_0 @ X23 @ X25)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.82           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['33', '34'])).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.58/0.82           = (k3_xboole_0 @ X20 @ X21))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.82           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf('38', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '37'])).
% 0.58/0.82  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['29', '38'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['21', '39'])).
% 0.58/0.82  thf(t46_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (![X18 : $i, X19 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.58/0.82          | ((k4_xboole_0 @ X2 @ X1) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '42'])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.82        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['4', '43'])).
% 0.58/0.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.82  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.82  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]:
% 0.58/0.82         ((r1_tarski @ X10 @ X11)
% 0.58/0.82          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.82  thf('49', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.58/0.82      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('51', plain, (((r1_tarski @ sk_A @ sk_B_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      (~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_A @ sk_B_1))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('53', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.82      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.58/0.82  thf('54', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.58/0.82      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf('56', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.58/0.82           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.58/0.82              (k3_xboole_0 @ X23 @ X25)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.58/0.82  thf('58', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0))
% 0.58/0.82           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['56', '57'])).
% 0.58/0.82  thf('59', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '37'])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.82           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.82  thf('62', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '37'])).
% 0.58/0.82  thf('63', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['61', '62'])).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ X0))
% 0.58/0.82           = (k3_xboole_0 @ sk_A @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['58', '63'])).
% 0.58/0.82  thf('65', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['55', '64'])).
% 0.58/0.82  thf(d7_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.58/0.82       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (![X7 : $i, X9 : $i]:
% 0.58/0.82         ((r1_xboole_0 @ X7 @ X9) | ((k3_xboole_0 @ X7 @ X9) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf('68', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.58/0.82      inference('simplify', [status(thm)], ['67'])).
% 0.58/0.82  thf('69', plain, ($false), inference('demod', [status(thm)], ['54', '68'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
