%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l8o2wQub77

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:19 EST 2020

% Result     : Theorem 6.71s
% Output     : Refutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 142 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  623 (1083 expanded)
%              Number of equality atoms :   60 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','41','42'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l8o2wQub77
% 0.14/0.36  % Computer   : n012.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:21:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 6.71/6.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.71/6.95  % Solved by: fo/fo7.sh
% 6.71/6.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.71/6.95  % done 4590 iterations in 6.485s
% 6.71/6.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.71/6.95  % SZS output start Refutation
% 6.71/6.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.71/6.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.71/6.95  thf(sk_A_type, type, sk_A: $i).
% 6.71/6.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.71/6.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.71/6.95  thf(sk_B_type, type, sk_B: $i).
% 6.71/6.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.71/6.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.71/6.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.71/6.95  thf(t77_xboole_1, conjecture,
% 6.71/6.95    (![A:$i,B:$i,C:$i]:
% 6.71/6.95     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.71/6.95          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 6.71/6.95  thf(zf_stmt_0, negated_conjecture,
% 6.71/6.95    (~( ![A:$i,B:$i,C:$i]:
% 6.71/6.95        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.71/6.95             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 6.71/6.95    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 6.71/6.95  thf('0', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 6.71/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.71/6.95  thf(t12_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i]:
% 6.71/6.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.71/6.95  thf('1', plain,
% 6.71/6.95      (![X11 : $i, X12 : $i]:
% 6.71/6.95         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 6.71/6.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.71/6.95  thf('2', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_C_1))),
% 6.71/6.95      inference('sup-', [status(thm)], ['0', '1'])).
% 6.71/6.95  thf(commutativity_k2_xboole_0, axiom,
% 6.71/6.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.71/6.95  thf('3', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.71/6.95  thf('4', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 6.71/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.71/6.95  thf(t23_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i,C:$i]:
% 6.71/6.95     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 6.71/6.95       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.71/6.95  thf('5', plain,
% 6.71/6.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 6.71/6.95              (k3_xboole_0 @ X18 @ X20)))),
% 6.71/6.95      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.71/6.95  thf('6', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 6.71/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.71/6.95  thf(d7_xboole_0, axiom,
% 6.71/6.95    (![A:$i,B:$i]:
% 6.71/6.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 6.71/6.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 6.71/6.95  thf('7', plain,
% 6.71/6.95      (![X4 : $i, X5 : $i]:
% 6.71/6.95         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 6.71/6.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.71/6.95  thf('8', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.71/6.95      inference('sup-', [status(thm)], ['6', '7'])).
% 6.71/6.95  thf('9', plain,
% 6.71/6.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 6.71/6.95              (k3_xboole_0 @ X18 @ X20)))),
% 6.71/6.95      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.71/6.95  thf('10', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 6.71/6.95           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 6.71/6.95      inference('sup+', [status(thm)], ['8', '9'])).
% 6.71/6.95  thf('11', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.71/6.95  thf(t2_boole, axiom,
% 6.71/6.95    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.71/6.95  thf('12', plain,
% 6.71/6.95      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 6.71/6.95      inference('cnf', [status(esa)], [t2_boole])).
% 6.71/6.95  thf(t22_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 6.71/6.95  thf('13', plain,
% 6.71/6.95      (![X16 : $i, X17 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 6.71/6.95      inference('cnf', [status(esa)], [t22_xboole_1])).
% 6.71/6.95  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['12', '13'])).
% 6.71/6.95  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['11', '14'])).
% 6.71/6.95  thf('16', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 6.71/6.95           = (k3_xboole_0 @ sk_A @ X0))),
% 6.71/6.95      inference('demod', [status(thm)], ['10', '15'])).
% 6.71/6.95  thf('17', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))
% 6.71/6.95           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 6.71/6.95      inference('sup+', [status(thm)], ['5', '16'])).
% 6.71/6.95  thf('18', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 6.71/6.95         = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 6.71/6.95      inference('sup+', [status(thm)], ['4', '17'])).
% 6.71/6.95  thf('19', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.71/6.95      inference('sup-', [status(thm)], ['6', '7'])).
% 6.71/6.95  thf(commutativity_k3_xboole_0, axiom,
% 6.71/6.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.71/6.95  thf('20', plain,
% 6.71/6.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.71/6.95  thf('21', plain,
% 6.71/6.95      (![X16 : $i, X17 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 6.71/6.95      inference('cnf', [status(esa)], [t22_xboole_1])).
% 6.71/6.95  thf('22', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['20', '21'])).
% 6.71/6.95  thf('23', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.71/6.95  thf(t7_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.71/6.95  thf('24', plain,
% 6.71/6.95      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 6.71/6.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.71/6.95  thf('25', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['23', '24'])).
% 6.71/6.95  thf('26', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.71/6.95      inference('sup+', [status(thm)], ['22', '25'])).
% 6.71/6.95  thf('27', plain,
% 6.71/6.95      (![X16 : $i, X17 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 6.71/6.95      inference('cnf', [status(esa)], [t22_xboole_1])).
% 6.71/6.95  thf('28', plain,
% 6.71/6.95      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 6.71/6.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.71/6.95  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.71/6.95      inference('sup+', [status(thm)], ['27', '28'])).
% 6.71/6.95  thf(t19_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i,C:$i]:
% 6.71/6.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 6.71/6.95       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.71/6.95  thf('30', plain,
% 6.71/6.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.71/6.95         (~ (r1_tarski @ X13 @ X14)
% 6.71/6.95          | ~ (r1_tarski @ X13 @ X15)
% 6.71/6.95          | (r1_tarski @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 6.71/6.95      inference('cnf', [status(esa)], [t19_xboole_1])).
% 6.71/6.95  thf('31', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 6.71/6.95      inference('sup-', [status(thm)], ['29', '30'])).
% 6.71/6.95  thf('32', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.71/6.95          (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 6.71/6.95      inference('sup-', [status(thm)], ['26', '31'])).
% 6.71/6.95  thf('33', plain,
% 6.71/6.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.71/6.95  thf('34', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.71/6.95          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.71/6.95      inference('demod', [status(thm)], ['32', '33'])).
% 6.71/6.95  thf('35', plain,
% 6.71/6.95      (![X11 : $i, X12 : $i]:
% 6.71/6.95         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 6.71/6.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.71/6.95  thf('36', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.71/6.95           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 6.71/6.95           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.71/6.95      inference('sup-', [status(thm)], ['34', '35'])).
% 6.71/6.95  thf('37', plain,
% 6.71/6.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.71/6.95  thf('38', plain,
% 6.71/6.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 6.71/6.95              (k3_xboole_0 @ X18 @ X20)))),
% 6.71/6.95      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.71/6.95  thf('39', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 6.71/6.95      inference('sup+', [status(thm)], ['37', '38'])).
% 6.71/6.95  thf('40', plain,
% 6.71/6.95      (![X16 : $i, X17 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 6.71/6.95      inference('cnf', [status(esa)], [t22_xboole_1])).
% 6.71/6.95  thf('41', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X0 @ X1)
% 6.71/6.95           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.71/6.95      inference('demod', [status(thm)], ['36', '39', '40'])).
% 6.71/6.95  thf('42', plain,
% 6.71/6.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.71/6.95  thf('43', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 6.71/6.95      inference('demod', [status(thm)], ['18', '19', '41', '42'])).
% 6.71/6.95  thf(t51_xboole_1, axiom,
% 6.71/6.95    (![A:$i,B:$i]:
% 6.71/6.95     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 6.71/6.95       ( A ) ))).
% 6.71/6.95  thf('44', plain,
% 6.71/6.95      (![X24 : $i, X25 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 6.71/6.95           = (X24))),
% 6.71/6.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.71/6.95  thf('45', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.71/6.95  thf('46', plain,
% 6.71/6.95      (![X24 : $i, X25 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ (k3_xboole_0 @ X24 @ X25))
% 6.71/6.95           = (X24))),
% 6.71/6.95      inference('demod', [status(thm)], ['44', '45'])).
% 6.71/6.95  thf('47', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.71/6.95      inference('sup-', [status(thm)], ['6', '7'])).
% 6.71/6.95  thf('48', plain,
% 6.71/6.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 6.71/6.95              (k3_xboole_0 @ X18 @ X20)))),
% 6.71/6.95      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.71/6.95  thf('49', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 6.71/6.95           = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['47', '48'])).
% 6.71/6.95  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.71/6.95      inference('sup+', [status(thm)], ['12', '13'])).
% 6.71/6.95  thf('51', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 6.71/6.95           = (k3_xboole_0 @ sk_A @ X0))),
% 6.71/6.95      inference('demod', [status(thm)], ['49', '50'])).
% 6.71/6.95  thf('52', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_A @ sk_B)
% 6.71/6.95         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 6.71/6.95      inference('sup+', [status(thm)], ['46', '51'])).
% 6.71/6.95  thf('53', plain,
% 6.71/6.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.71/6.95  thf('54', plain,
% 6.71/6.95      (((k3_xboole_0 @ sk_B @ sk_A)
% 6.71/6.95         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 6.71/6.95      inference('demod', [status(thm)], ['52', '53'])).
% 6.71/6.95  thf('55', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         ((k3_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 6.71/6.95           = (k3_xboole_0 @ sk_A @ X0))),
% 6.71/6.95      inference('demod', [status(thm)], ['10', '15'])).
% 6.71/6.95  thf('56', plain,
% 6.71/6.95      (![X4 : $i, X6 : $i]:
% 6.71/6.95         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 6.71/6.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.71/6.95  thf('57', plain,
% 6.71/6.95      (![X0 : $i]:
% 6.71/6.95         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 6.71/6.95          | (r1_xboole_0 @ sk_A @ 
% 6.71/6.95             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0)))),
% 6.71/6.95      inference('sup-', [status(thm)], ['55', '56'])).
% 6.71/6.95  thf('58', plain,
% 6.71/6.95      ((((k3_xboole_0 @ sk_B @ sk_A) != (k1_xboole_0))
% 6.71/6.95        | (r1_xboole_0 @ sk_A @ 
% 6.71/6.95           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 6.71/6.95            (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 6.71/6.95      inference('sup-', [status(thm)], ['54', '57'])).
% 6.71/6.95  thf('59', plain,
% 6.71/6.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.71/6.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.71/6.95  thf('60', plain,
% 6.71/6.95      (![X24 : $i, X25 : $i]:
% 6.71/6.95         ((k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ (k3_xboole_0 @ X24 @ X25))
% 6.71/6.95           = (X24))),
% 6.71/6.95      inference('demod', [status(thm)], ['44', '45'])).
% 6.71/6.95  thf('61', plain,
% 6.71/6.95      ((((k3_xboole_0 @ sk_B @ sk_A) != (k1_xboole_0))
% 6.71/6.95        | (r1_xboole_0 @ sk_A @ sk_B))),
% 6.71/6.95      inference('demod', [status(thm)], ['58', '59', '60'])).
% 6.71/6.95  thf('62', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 6.71/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.71/6.95  thf('63', plain, (((k3_xboole_0 @ sk_B @ sk_A) != (k1_xboole_0))),
% 6.71/6.95      inference('clc', [status(thm)], ['61', '62'])).
% 6.71/6.95  thf('64', plain, ($false),
% 6.71/6.95      inference('simplify_reflect-', [status(thm)], ['43', '63'])).
% 6.71/6.95  
% 6.71/6.95  % SZS output end Refutation
% 6.71/6.95  
% 6.71/6.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
