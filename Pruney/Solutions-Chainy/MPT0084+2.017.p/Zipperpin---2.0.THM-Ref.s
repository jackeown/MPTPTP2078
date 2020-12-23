%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pPISsrNMWf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:21 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 363 expanded)
%              Number of leaves         :   16 ( 129 expanded)
%              Depth                    :   19
%              Number of atoms          :  912 (2770 expanded)
%              Number of equality atoms :  107 ( 310 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 ) )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','54'])).

thf('56',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('68',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('70',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('72',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('94',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('97',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('100',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','65','72','73','97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pPISsrNMWf
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.72/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.91  % Solved by: fo/fo7.sh
% 0.72/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.91  % done 914 iterations in 0.451s
% 0.72/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.91  % SZS output start Refutation
% 0.72/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.91  thf(t77_xboole_1, conjecture,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.72/0.91          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.72/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.91        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.72/0.91             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.72/0.91    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.72/0.91  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(t3_boole, axiom,
% 0.72/0.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.72/0.91  thf('1', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.72/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.91  thf(t48_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.91  thf('2', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('3', plain,
% 0.72/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('4', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(d7_xboole_0, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.72/0.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.72/0.91  thf('5', plain,
% 0.72/0.91      (![X2 : $i, X3 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.72/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.91  thf('6', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.72/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.72/0.91  thf('7', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf(t47_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.72/0.91  thf('8', plain,
% 0.72/0.91      (![X9 : $i, X10 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.72/0.91           = (k4_xboole_0 @ X9 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.91  thf('9', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.72/0.91           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('sup+', [status(thm)], ['7', '8'])).
% 0.72/0.91  thf('10', plain,
% 0.72/0.91      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)
% 0.72/0.91         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.72/0.91      inference('sup+', [status(thm)], ['6', '9'])).
% 0.72/0.91  thf(t49_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.72/0.91       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.72/0.91  thf('11', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('12', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.72/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.91  thf('13', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('14', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.72/0.91         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.72/0.91      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.72/0.91  thf('15', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('16', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ sk_B @ 
% 0.72/0.91           (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ X0))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['14', '15'])).
% 0.72/0.91  thf('17', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('18', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ sk_B @ 
% 0.72/0.91           (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ X0))
% 0.72/0.91           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.72/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.72/0.91  thf('19', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_B @ 
% 0.72/0.91         (k3_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0))
% 0.72/0.91         = (k3_xboole_0 @ sk_B @ 
% 0.72/0.91            (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))))),
% 0.72/0.91      inference('sup+', [status(thm)], ['3', '18'])).
% 0.72/0.91  thf('20', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('21', plain,
% 0.72/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('22', plain,
% 0.72/0.91      (![X9 : $i, X10 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.72/0.91           = (k4_xboole_0 @ X9 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.91  thf('23', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.72/0.91           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['21', '22'])).
% 0.72/0.91  thf('24', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('25', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.72/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.91  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.72/0.91      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.72/0.91  thf('27', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(l32_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.91  thf('28', plain,
% 0.72/0.91      (![X5 : $i, X7 : $i]:
% 0.72/0.91         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.72/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.91  thf('29', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.72/0.91  thf('30', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('31', plain,
% 0.72/0.91      (![X5 : $i, X6 : $i]:
% 0.72/0.91         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.72/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.91  thf('32', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.72/0.91          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['30', '31'])).
% 0.72/0.91  thf('33', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.72/0.91          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C))),
% 0.72/0.91      inference('sup-', [status(thm)], ['29', '32'])).
% 0.72/0.91  thf('34', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.91        | (r1_tarski @ (k3_xboole_0 @ k1_xboole_0 @ sk_A) @ sk_C))),
% 0.72/0.91      inference('sup-', [status(thm)], ['26', '33'])).
% 0.72/0.91  thf('35', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.72/0.91  thf('36', plain,
% 0.72/0.91      (![X9 : $i, X10 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.72/0.91           = (k4_xboole_0 @ X9 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.91  thf('37', plain,
% 0.72/0.91      (![X5 : $i, X6 : $i]:
% 0.72/0.91         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.72/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.91  thf('38', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.72/0.91          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.91  thf('39', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.91        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['35', '38'])).
% 0.72/0.91  thf('40', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('41', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.91        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.72/0.91      inference('demod', [status(thm)], ['39', '40'])).
% 0.72/0.91  thf('42', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))),
% 0.72/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.72/0.91  thf('43', plain,
% 0.72/0.91      (![X5 : $i, X7 : $i]:
% 0.72/0.91         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.72/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.91  thf('44', plain,
% 0.72/0.91      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['42', '43'])).
% 0.72/0.91  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.72/0.91  thf('46', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('47', plain,
% 0.72/0.91      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.72/0.91      inference('sup+', [status(thm)], ['45', '46'])).
% 0.72/0.91  thf('48', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.72/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.72/0.91  thf('49', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('50', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.72/0.91  thf('51', plain, (((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.72/0.91      inference('demod', [status(thm)], ['44', '50'])).
% 0.72/0.91  thf('52', plain,
% 0.72/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('53', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('54', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.72/0.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.72/0.91  thf('55', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ sk_C))),
% 0.72/0.91      inference('demod', [status(thm)], ['34', '54'])).
% 0.72/0.91  thf('56', plain, ((r1_tarski @ k1_xboole_0 @ sk_C)),
% 0.72/0.91      inference('simplify', [status(thm)], ['55'])).
% 0.72/0.91  thf('57', plain,
% 0.72/0.91      (![X5 : $i, X7 : $i]:
% 0.72/0.91         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.72/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.91  thf('58', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['56', '57'])).
% 0.72/0.91  thf('59', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('60', plain,
% 0.72/0.91      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.72/0.91         = (k3_xboole_0 @ k1_xboole_0 @ sk_C))),
% 0.72/0.91      inference('sup+', [status(thm)], ['58', '59'])).
% 0.72/0.91  thf('61', plain,
% 0.72/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('62', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.72/0.91      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.72/0.91  thf('63', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_C))),
% 0.72/0.91      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.72/0.91  thf('64', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('65', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ X0))
% 0.72/0.91           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['63', '64'])).
% 0.72/0.91  thf('66', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.72/0.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.72/0.91  thf('67', plain,
% 0.72/0.91      (![X9 : $i, X10 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.72/0.91           = (k4_xboole_0 @ X9 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.91  thf('68', plain,
% 0.72/0.91      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.72/0.91         = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.72/0.91      inference('sup+', [status(thm)], ['66', '67'])).
% 0.72/0.91  thf('69', plain,
% 0.72/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('70', plain,
% 0.72/0.91      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.72/0.91         = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['68', '69'])).
% 0.72/0.91  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.72/0.91      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.72/0.91  thf('72', plain, (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['70', '71'])).
% 0.72/0.91  thf('73', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('74', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.72/0.91         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.72/0.91      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.72/0.91  thf('75', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('76', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('77', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X2 @ 
% 0.72/0.91           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.72/0.91           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['75', '76'])).
% 0.72/0.91  thf('78', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('79', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X2 @ 
% 0.72/0.91           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.72/0.91           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.72/0.91      inference('demod', [status(thm)], ['77', '78'])).
% 0.72/0.91  thf('80', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_B @ 
% 0.72/0.91         (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.72/0.91         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.72/0.91      inference('sup+', [status(thm)], ['74', '79'])).
% 0.72/0.91  thf('81', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.72/0.91           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('sup+', [status(thm)], ['7', '8'])).
% 0.72/0.91  thf('82', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('83', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.91  thf('84', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.72/0.91      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.72/0.91  thf('85', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.91  thf('86', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('87', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ sk_A @ 
% 0.72/0.91           (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.72/0.91           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.72/0.91      inference('sup+', [status(thm)], ['85', '86'])).
% 0.72/0.91  thf('88', plain,
% 0.72/0.91      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.72/0.91      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.72/0.91  thf('89', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ sk_A @ 
% 0.72/0.91           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))
% 0.72/0.91           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.72/0.91      inference('demod', [status(thm)], ['87', '88'])).
% 0.72/0.91  thf('90', plain,
% 0.72/0.91      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.72/0.91      inference('sup+', [status(thm)], ['84', '89'])).
% 0.72/0.91  thf('91', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('92', plain,
% 0.72/0.91      (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k4_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.72/0.91      inference('demod', [status(thm)], ['90', '91'])).
% 0.72/0.91  thf('93', plain,
% 0.72/0.91      (![X9 : $i, X10 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.72/0.91           = (k4_xboole_0 @ X9 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.91  thf('94', plain,
% 0.72/0.91      (((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.72/0.91         = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.72/0.91      inference('sup+', [status(thm)], ['92', '93'])).
% 0.72/0.91  thf('95', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('96', plain, (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['70', '71'])).
% 0.72/0.91  thf('97', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.72/0.91      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.72/0.91  thf('98', plain,
% 0.72/0.91      (![X11 : $i, X12 : $i]:
% 0.72/0.91         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.72/0.91           = (k3_xboole_0 @ X11 @ X12))),
% 0.72/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.91  thf('99', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.72/0.91  thf('100', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)],
% 0.72/0.91                ['19', '20', '65', '72', '73', '97', '98', '99'])).
% 0.72/0.91  thf('101', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('102', plain,
% 0.72/0.91      (![X2 : $i, X4 : $i]:
% 0.72/0.91         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.72/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.91  thf('103', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('sup-', [status(thm)], ['101', '102'])).
% 0.72/0.91  thf('104', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.72/0.91      inference('sup-', [status(thm)], ['100', '103'])).
% 0.72/0.91  thf('105', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.72/0.91      inference('simplify', [status(thm)], ['104'])).
% 0.72/0.91  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.72/0.91  
% 0.72/0.91  % SZS output end Refutation
% 0.72/0.91  
% 0.72/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
