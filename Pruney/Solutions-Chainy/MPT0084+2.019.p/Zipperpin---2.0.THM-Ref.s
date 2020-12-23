%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oHiZKI0bXs

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:21 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  653 (1443 expanded)
%              Number of equality atoms :   75 ( 167 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51','52','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oHiZKI0bXs
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:55:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 326 iterations in 0.155s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(t77_xboole_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.37/0.57          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.57        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.37/0.57             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.37/0.57  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d7_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf(t3_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.57  thf('10', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('17', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf(t49_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.37/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.37/0.57         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['3', '20'])).
% 0.37/0.57  thf('22', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.57  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.37/0.57           = (k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['26', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.37/0.57         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['23', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.37/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.37/0.57         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '38'])).
% 0.37/0.57  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.57  thf(l32_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.37/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.37/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['39', '47'])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      (![X5 : $i, X7 : $i]:
% 0.37/0.57         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.37/0.57         (k4_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.37/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('55', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      (![X5 : $i, X7 : $i]:
% 0.37/0.57         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.57  thf('57', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.57      inference('sup+', [status(thm)], ['57', '58'])).
% 0.37/0.57  thf('60', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('62', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.37/0.57           = (k4_xboole_0 @ sk_A @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.37/0.57           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['54', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.37/0.57           = (k3_xboole_0 @ sk_A @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A))
% 0.37/0.57           = (k3_xboole_0 @ sk_A @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['53', '67'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('70', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['50', '51', '52', '68', '69'])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      (![X2 : $i, X4 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['70', '73'])).
% 0.37/0.57  thf('75', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.57      inference('simplify', [status(thm)], ['74'])).
% 0.37/0.57  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
