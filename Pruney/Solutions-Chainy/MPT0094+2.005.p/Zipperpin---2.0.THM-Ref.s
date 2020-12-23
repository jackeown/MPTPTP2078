%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2TVuh0JX2V

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:49 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 189 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  614 (1418 expanded)
%              Number of equality atoms :   72 ( 177 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t87_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
          = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ( ( k4_xboole_0 @ X14 @ X16 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
     != sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('57',plain,
    ( ( sk_B != sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2TVuh0JX2V
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.12/2.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.12/2.33  % Solved by: fo/fo7.sh
% 2.12/2.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.33  % done 3886 iterations in 1.890s
% 2.12/2.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.12/2.33  % SZS output start Refutation
% 2.12/2.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.12/2.33  thf(sk_B_type, type, sk_B: $i).
% 2.12/2.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.12/2.33  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.12/2.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.12/2.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.12/2.33  thf(sk_C_type, type, sk_C: $i).
% 2.12/2.33  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.33  thf(t87_xboole_1, conjecture,
% 2.12/2.33    (![A:$i,B:$i,C:$i]:
% 2.12/2.33     ( ( r1_xboole_0 @ A @ B ) =>
% 2.12/2.33       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 2.12/2.33         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 2.12/2.33  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.33    (~( ![A:$i,B:$i,C:$i]:
% 2.12/2.33        ( ( r1_xboole_0 @ A @ B ) =>
% 2.12/2.33          ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 2.12/2.33            ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )),
% 2.12/2.33    inference('cnf.neg', [status(esa)], [t87_xboole_1])).
% 2.12/2.33  thf('0', plain,
% 2.12/2.33      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 2.12/2.33         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 2.12/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.33  thf(commutativity_k2_xboole_0, axiom,
% 2.12/2.33    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.12/2.33  thf('1', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('2', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('3', plain,
% 2.12/2.33      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.12/2.33         != (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 2.12/2.33      inference('demod', [status(thm)], ['0', '1', '2'])).
% 2.12/2.33  thf(t3_boole, axiom,
% 2.12/2.33    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.12/2.33  thf('4', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.12/2.33      inference('cnf', [status(esa)], [t3_boole])).
% 2.12/2.33  thf(t48_xboole_1, axiom,
% 2.12/2.33    (![A:$i,B:$i]:
% 2.12/2.33     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.12/2.33  thf('5', plain,
% 2.12/2.33      (![X9 : $i, X10 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.12/2.33           = (k3_xboole_0 @ X9 @ X10))),
% 2.12/2.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.12/2.33  thf('6', plain,
% 2.12/2.33      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['4', '5'])).
% 2.12/2.33  thf(t2_boole, axiom,
% 2.12/2.33    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.12/2.33  thf('7', plain,
% 2.12/2.33      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.33      inference('cnf', [status(esa)], [t2_boole])).
% 2.12/2.33  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.12/2.33      inference('demod', [status(thm)], ['6', '7'])).
% 2.12/2.33  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.12/2.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.33  thf(t83_xboole_1, axiom,
% 2.12/2.33    (![A:$i,B:$i]:
% 2.12/2.33     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.12/2.33  thf('10', plain,
% 2.12/2.33      (![X14 : $i, X15 : $i]:
% 2.12/2.33         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 2.12/2.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.12/2.33  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.12/2.33      inference('sup-', [status(thm)], ['9', '10'])).
% 2.12/2.33  thf(t42_xboole_1, axiom,
% 2.12/2.33    (![A:$i,B:$i,C:$i]:
% 2.12/2.33     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.12/2.33       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.12/2.33  thf('12', plain,
% 2.12/2.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X8) @ X7)
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X8 @ X7)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.12/2.33  thf('13', plain,
% 2.12/2.33      (![X0 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 2.12/2.33           = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['11', '12'])).
% 2.12/2.33  thf(t39_xboole_1, axiom,
% 2.12/2.33    (![A:$i,B:$i]:
% 2.12/2.33     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.12/2.33  thf('14', plain,
% 2.12/2.33      (![X3 : $i, X4 : $i]:
% 2.12/2.33         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 2.12/2.33           = (k2_xboole_0 @ X3 @ X4))),
% 2.12/2.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.12/2.33  thf('15', plain,
% 2.12/2.33      (![X0 : $i]:
% 2.12/2.33         ((k2_xboole_0 @ sk_B @ 
% 2.12/2.33           (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))
% 2.12/2.33           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['13', '14'])).
% 2.12/2.33  thf('16', plain,
% 2.12/2.33      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ k1_xboole_0))
% 2.12/2.33         = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['8', '15'])).
% 2.12/2.33  thf('17', plain,
% 2.12/2.33      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.33      inference('cnf', [status(esa)], [t2_boole])).
% 2.12/2.33  thf(t52_xboole_1, axiom,
% 2.12/2.33    (![A:$i,B:$i,C:$i]:
% 2.12/2.33     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.12/2.33       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.12/2.33  thf('18', plain,
% 2.12/2.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 2.12/2.33              (k3_xboole_0 @ X11 @ X13)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.12/2.33  thf('19', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['17', '18'])).
% 2.12/2.33  thf('20', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.12/2.33      inference('cnf', [status(esa)], [t3_boole])).
% 2.12/2.33  thf('21', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('22', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X0 @ X1)
% 2.12/2.33           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.12/2.33      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.12/2.33  thf('23', plain,
% 2.12/2.33      (![X3 : $i, X4 : $i]:
% 2.12/2.33         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 2.12/2.33           = (k2_xboole_0 @ X3 @ X4))),
% 2.12/2.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.12/2.33  thf('24', plain,
% 2.12/2.33      (![X0 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['22', '23'])).
% 2.12/2.33  thf('25', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.12/2.33      inference('cnf', [status(esa)], [t3_boole])).
% 2.12/2.33  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['24', '25'])).
% 2.12/2.33  thf('27', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['26', '27'])).
% 2.12/2.33  thf('29', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('30', plain,
% 2.12/2.33      (((k2_xboole_0 @ sk_A @ sk_B)
% 2.12/2.33         = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.12/2.33      inference('demod', [status(thm)], ['16', '28', '29'])).
% 2.12/2.33  thf('31', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.12/2.33      inference('demod', [status(thm)], ['6', '7'])).
% 2.12/2.33  thf('33', plain,
% 2.12/2.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X8) @ X7)
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X8 @ X7)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.12/2.33  thf('34', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 2.12/2.33           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['32', '33'])).
% 2.12/2.33  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['24', '25'])).
% 2.12/2.33  thf('36', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 2.12/2.33           = (k4_xboole_0 @ X1 @ X0))),
% 2.12/2.33      inference('demod', [status(thm)], ['34', '35'])).
% 2.12/2.33  thf('37', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.12/2.33           = (k4_xboole_0 @ X1 @ X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['31', '36'])).
% 2.12/2.33  thf('38', plain,
% 2.12/2.33      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 2.12/2.33         (k2_xboole_0 @ sk_A @ sk_B))
% 2.12/2.33         = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['30', '37'])).
% 2.12/2.33  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.12/2.33      inference('demod', [status(thm)], ['6', '7'])).
% 2.12/2.33  thf('40', plain,
% 2.12/2.33      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.12/2.33      inference('demod', [status(thm)], ['38', '39'])).
% 2.12/2.33  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.12/2.33      inference('demod', [status(thm)], ['6', '7'])).
% 2.12/2.33  thf('42', plain,
% 2.12/2.33      (![X9 : $i, X10 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.12/2.33           = (k3_xboole_0 @ X9 @ X10))),
% 2.12/2.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.12/2.33  thf('43', plain,
% 2.12/2.33      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['41', '42'])).
% 2.12/2.33  thf('44', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.12/2.33      inference('cnf', [status(esa)], [t3_boole])).
% 2.12/2.33  thf('45', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.12/2.33      inference('demod', [status(thm)], ['43', '44'])).
% 2.12/2.33  thf('46', plain,
% 2.12/2.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 2.12/2.33              (k3_xboole_0 @ X11 @ X13)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.12/2.33  thf('47', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['45', '46'])).
% 2.12/2.33  thf('48', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.33  thf('49', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.12/2.33           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.12/2.33      inference('demod', [status(thm)], ['47', '48'])).
% 2.12/2.33  thf('50', plain,
% 2.12/2.33      (![X14 : $i, X16 : $i]:
% 2.12/2.33         ((r1_xboole_0 @ X14 @ X16) | ((k4_xboole_0 @ X14 @ X16) != (X14)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.12/2.33  thf('51', plain,
% 2.12/2.33      (![X0 : $i, X1 : $i]:
% 2.12/2.33         (((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) != (X1))
% 2.12/2.33          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.12/2.33      inference('sup-', [status(thm)], ['49', '50'])).
% 2.12/2.33  thf('52', plain,
% 2.12/2.33      ((((k2_xboole_0 @ sk_B @ k1_xboole_0) != (sk_B))
% 2.12/2.33        | (r1_xboole_0 @ sk_B @ 
% 2.12/2.33           (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)))),
% 2.12/2.33      inference('sup-', [status(thm)], ['40', '51'])).
% 2.12/2.33  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['26', '27'])).
% 2.12/2.33  thf('54', plain,
% 2.12/2.33      (![X0 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 2.12/2.33           = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['11', '12'])).
% 2.12/2.33  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.12/2.33      inference('demod', [status(thm)], ['6', '7'])).
% 2.12/2.33  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.12/2.33      inference('sup+', [status(thm)], ['26', '27'])).
% 2.12/2.33  thf('57', plain, ((((sk_B) != (sk_B)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.12/2.33      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 2.12/2.33  thf('58', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.12/2.33      inference('simplify', [status(thm)], ['57'])).
% 2.12/2.33  thf('59', plain,
% 2.12/2.33      (![X14 : $i, X15 : $i]:
% 2.12/2.33         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 2.12/2.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.12/2.33  thf('60', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.12/2.33      inference('sup-', [status(thm)], ['58', '59'])).
% 2.12/2.33  thf('61', plain,
% 2.12/2.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X8) @ X7)
% 2.12/2.33           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X8 @ X7)))),
% 2.12/2.33      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.12/2.33  thf('62', plain,
% 2.12/2.33      (![X0 : $i]:
% 2.12/2.33         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 2.12/2.33           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 2.12/2.33      inference('sup+', [status(thm)], ['60', '61'])).
% 2.12/2.33  thf('63', plain,
% 2.12/2.33      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.12/2.33         != (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 2.12/2.33      inference('demod', [status(thm)], ['3', '62'])).
% 2.12/2.33  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 2.12/2.33  
% 2.12/2.33  % SZS output end Refutation
% 2.12/2.33  
% 2.21/2.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
