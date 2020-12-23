%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8YvYvK5XJV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  707 (1198 expanded)
%              Number of equality atoms :   80 ( 120 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('51',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('59',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_A )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_A )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','66'])).

thf('68',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8YvYvK5XJV
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 295 iterations in 0.115s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(t95_relat_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ B ) =>
% 0.22/0.58       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.58         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i]:
% 0.22/0.58        ( ( v1_relat_1 @ B ) =>
% 0.22/0.58          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.58            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.58        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.58       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.58        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('split', [status(esa)], ['2'])).
% 0.22/0.58  thf(t90_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ B ) =>
% 0.22/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      (![X21 : $i, X22 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.22/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.22/0.58          | ~ (v1_relat_1 @ X21))),
% 0.22/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (((((k1_relat_1 @ k1_xboole_0)
% 0.22/0.58           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.58         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.58  thf(t60_relat_1, axiom,
% 0.22/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.58  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.22/0.58  thf(t47_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X7 : $i, X8 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.22/0.58           = (k4_xboole_0 @ X7 @ X8))),
% 0.22/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.22/0.58          = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.58  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(t87_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ B ) =>
% 0.22/0.58       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.22/0.58  thf('13', plain,
% 0.22/0.58      (![X19 : $i, X20 : $i]:
% 0.22/0.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X19 @ X20)) @ X20)
% 0.22/0.58          | ~ (v1_relat_1 @ X19))),
% 0.22/0.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.22/0.58  thf(l32_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k4_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.22/0.58              = (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.58  thf(t79_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.22/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.58  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X2 : $i, X3 : $i]:
% 0.22/0.58         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((r1_xboole_0 @ X0 @ k1_xboole_0) | ~ (v1_relat_1 @ X1))),
% 0.22/0.58      inference('sup+', [status(thm)], ['15', '18'])).
% 0.22/0.58  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['12', '19'])).
% 0.22/0.58  thf(t83_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.58  thf('21', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.58  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('demod', [status(thm)], ['11', '22'])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.58         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.58         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.58       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.58       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('split', [status(esa)], ['2'])).
% 0.22/0.58  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k4_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.22/0.58              = (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.22/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (v1_relat_1 @ X1))),
% 0.22/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.58  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.58  thf(t48_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.58           = (k3_xboole_0 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.58           = (k3_xboole_0 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.58  thf('41', plain,
% 0.22/0.58      (![X4 : $i, X5 : $i]:
% 0.22/0.58         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.58  thf('42', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.58          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.58          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.58  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.58  thf('45', plain,
% 0.22/0.58      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.58  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.58  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.58  thf('49', plain,
% 0.22/0.58      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('split', [status(esa)], ['2'])).
% 0.22/0.58  thf('50', plain,
% 0.22/0.58      (![X2 : $i, X3 : $i]:
% 0.22/0.58         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.58  thf('51', plain,
% 0.22/0.58      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.58  thf('52', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.58  thf('53', plain,
% 0.22/0.58      ((((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A)))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.58  thf('54', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.58           = (k3_xboole_0 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.58  thf('55', plain,
% 0.22/0.58      ((((k4_xboole_0 @ sk_A @ sk_A)
% 0.22/0.58          = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['53', '54'])).
% 0.22/0.58  thf('56', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.58  thf(dt_k7_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.58  thf('57', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.22/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.58  thf('58', plain,
% 0.22/0.58      (![X21 : $i, X22 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.22/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.22/0.58          | ~ (v1_relat_1 @ X21))),
% 0.22/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.58  thf(t64_relat_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) =>
% 0.22/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.58  thf('59', plain,
% 0.22/0.58      (![X18 : $i]:
% 0.22/0.58         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.22/0.58          | ((X18) = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.58  thf('60', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.58          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.58  thf('61', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['57', '60'])).
% 0.22/0.58  thf('62', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.22/0.58          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X1))),
% 0.22/0.58      inference('simplify', [status(thm)], ['61'])).
% 0.22/0.58  thf('63', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0)
% 0.22/0.58          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['56', '62'])).
% 0.22/0.58  thf('64', plain,
% 0.22/0.58      (((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))
% 0.22/0.58         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.22/0.58         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['55', '63'])).
% 0.22/0.58  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('66', plain,
% 0.22/0.58      (((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))
% 0.22/0.58         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.58  thf('67', plain,
% 0.22/0.58      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.58         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['48', '66'])).
% 0.22/0.58  thf('68', plain,
% 0.22/0.58      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.58         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.58  thf('69', plain,
% 0.22/0.58      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.22/0.58         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('70', plain,
% 0.22/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.58         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.58             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.58  thf('71', plain,
% 0.22/0.58      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.58       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.58  thf('72', plain, ($false),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '71'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
