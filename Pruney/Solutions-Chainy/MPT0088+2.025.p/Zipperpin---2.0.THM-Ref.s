%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lKUvJA3oqd

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:38 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 132 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  645 (1046 expanded)
%              Number of equality atoms :   61 (  99 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('53',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('64',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','62','63'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lKUvJA3oqd
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 2476 iterations in 0.731s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.18  thf(t81_xboole_1, conjecture,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.00/1.18       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i,B:$i,C:$i]:
% 1.00/1.18        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.00/1.18          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.00/1.18  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(t48_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.18           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf('2', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.18           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf(t79_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.00/1.18  thf('3', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.00/1.18  thf(symmetry_r1_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X3 : $i, X4 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.00/1.18  thf('5', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.00/1.18  thf(d7_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.00/1.18       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.18  thf(t47_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      (![X6 : $i, X7 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 1.00/1.18           = (k4_xboole_0 @ X6 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.00/1.18           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['7', '8'])).
% 1.00/1.18  thf(t3_boole, axiom,
% 1.00/1.18    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.00/1.18  thf('10', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.18  thf('11', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['9', '10'])).
% 1.00/1.18  thf('12', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['2', '11'])).
% 1.00/1.18  thf(t49_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.00/1.18       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.00/1.18           = (k4_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 1.00/1.18           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['14', '15'])).
% 1.00/1.18  thf('17', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('20', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.18           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X2 @ 
% 1.00/1.18           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 1.00/1.18           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['20', '21'])).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X2 @ 
% 1.00/1.18           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.00/1.18           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['22', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 1.00/1.18         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 1.00/1.18      inference('sup+', [status(thm)], ['19', '24'])).
% 1.00/1.18  thf('26', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.18  thf('27', plain,
% 1.00/1.18      (((k3_xboole_0 @ sk_A @ sk_B)
% 1.00/1.18         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 1.00/1.18      inference('demod', [status(thm)], ['25', '26'])).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['9', '10'])).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.00/1.18      inference('sup+', [status(thm)], ['29', '30'])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['28', '31'])).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k4_xboole_0 @ X0 @ sk_C))),
% 1.00/1.18      inference('sup+', [status(thm)], ['27', '32'])).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.18  thf('35', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 1.00/1.18           (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 1.00/1.18           sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['16', '35'])).
% 1.00/1.18  thf('37', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('39', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ sk_A @ 
% 1.00/1.18           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)) = (k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.00/1.18  thf('40', plain,
% 1.00/1.18      (![X6 : $i, X7 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 1.00/1.18           = (k4_xboole_0 @ X6 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.18  thf('41', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.00/1.18           = (k4_xboole_0 @ sk_A @ 
% 1.00/1.18              (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['39', '40'])).
% 1.00/1.18  thf('42', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.18  thf('43', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((sk_A)
% 1.00/1.18           = (k4_xboole_0 @ sk_A @ 
% 1.00/1.18              (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 1.00/1.18      inference('demod', [status(thm)], ['41', '42'])).
% 1.00/1.18  thf('44', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((sk_A)
% 1.00/1.18           = (k4_xboole_0 @ sk_A @ 
% 1.00/1.18              (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['1', '43'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((sk_A)
% 1.00/1.18           = (k4_xboole_0 @ sk_A @ 
% 1.00/1.18              (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 1.00/1.18      inference('demod', [status(thm)], ['44', '45'])).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X2 @ 
% 1.00/1.18           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.00/1.18           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['22', '23'])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      (((k3_xboole_0 @ sk_B @ sk_A)
% 1.00/1.18         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.00/1.18      inference('sup+', [status(thm)], ['46', '47'])).
% 1.00/1.18  thf('49', plain,
% 1.00/1.18      (![X6 : $i, X7 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 1.00/1.18           = (k4_xboole_0 @ X6 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.18  thf('50', plain,
% 1.00/1.18      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.00/1.18         (k3_xboole_0 @ sk_B @ sk_A))
% 1.00/1.18         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.00/1.18      inference('sup+', [status(thm)], ['48', '49'])).
% 1.00/1.18  thf('51', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('53', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.18  thf('54', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.18           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf('55', plain,
% 1.00/1.18      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['53', '54'])).
% 1.00/1.18  thf('56', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.18  thf('57', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.00/1.18  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.00/1.18      inference('sup+', [status(thm)], ['56', '57'])).
% 1.00/1.18  thf('59', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.18  thf('60', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['58', '59'])).
% 1.00/1.18  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['55', '60'])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.00/1.18           = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['52', '61'])).
% 1.00/1.18  thf('63', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 1.00/1.18           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.00/1.18  thf('64', plain,
% 1.00/1.18      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.00/1.18      inference('demod', [status(thm)], ['50', '51', '62', '63'])).
% 1.00/1.18  thf('65', plain,
% 1.00/1.18      (![X0 : $i, X2 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.18  thf('66', plain,
% 1.00/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.18        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['64', '65'])).
% 1.00/1.18  thf('67', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.00/1.18      inference('simplify', [status(thm)], ['66'])).
% 1.00/1.18  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
