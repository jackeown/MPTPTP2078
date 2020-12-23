%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NPq7U3shzX

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 266 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  629 (2116 expanded)
%              Number of equality atoms :   81 ( 274 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','37','38','39','40','41','42','43','44'])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','37','38','39','40','41','42','43','44'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('68',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['57','67'])).

thf('69',plain,(
    sk_A = sk_C ),
    inference('sup+',[status(thm)],['56','68'])).

thf('70',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NPq7U3shzX
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 304 iterations in 0.163s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(t71_xboole_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.43/0.61         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.43/0.61       ( ( A ) = ( C ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.43/0.61            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.43/0.61          ( ( A ) = ( C ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t40_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.43/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.43/0.61         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.43/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf(t48_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.61           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.43/0.61         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d7_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.43/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.61  thf('9', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '9'])).
% 0.43/0.61  thf(t39_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.61           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.43/0.61         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.43/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.61  thf(t3_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.61  thf('14', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf('16', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.43/0.61         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['12', '17', '18'])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.61           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.43/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.43/0.61           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.43/0.61         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 0.43/0.61         = (k4_xboole_0 @ sk_C @ 
% 0.43/0.61            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['19', '22'])).
% 0.43/0.61  thf(t41_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.43/0.61           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.43/0.61           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.61  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.61           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf(t2_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.61  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.43/0.61           = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['28', '33'])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.61           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['27', '36'])).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.43/0.61           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.61  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.43/0.61           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['27', '36'])).
% 0.43/0.61  thf('44', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_C))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['23', '24', '25', '26', '37', '38', '39', '40', '41', '42', 
% 0.43/0.61                 '43', '44'])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.61           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf('48', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.61  thf('50', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('51', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['47', '50'])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.61           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('56', plain, (((sk_C) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.43/0.61  thf('57', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_C))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['23', '24', '25', '26', '37', '38', '39', '40', '41', '42', 
% 0.43/0.61                 '43', '44'])).
% 0.43/0.61  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.43/0.61           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.61           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.61           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['59', '60'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.43/0.61           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['58', '61'])).
% 0.43/0.61  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.43/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.43/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['64', '65'])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.43/0.61  thf('68', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['57', '67'])).
% 0.43/0.61  thf('69', plain, (((sk_A) = (sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['56', '68'])).
% 0.43/0.61  thf('70', plain, (((sk_A) != (sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('71', plain, ($false),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
