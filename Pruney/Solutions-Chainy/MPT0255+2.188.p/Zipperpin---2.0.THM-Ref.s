%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.obVydL05N8

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:18 EST 2020

% Result     : Theorem 8.19s
% Output     : Refutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  253 (10769 expanded)
%              Number of leaves         :   22 (3604 expanded)
%              Depth                    :   34
%              Number of atoms          : 2806 (119122 expanded)
%              Number of equality atoms :  280 (11972 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X1 ) )
       != ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X1 ) )
       != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) )
       != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
       != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','60'])).

thf('62',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('74',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('75',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('77',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','72','73','74','75','76'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X5 ) ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X5 @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X4 @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('99',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','95'])).

thf('101',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','96','99','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['8','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ k1_xboole_0 ) )
       != ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','95'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('120',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['117','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('129',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) )
       != ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
       != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('141',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) )
       != ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) )
       != ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['151','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['150','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','163'])).

thf('165',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('166',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('167',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('168',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('172',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('175',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('176',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('177',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','173','174','175','182','183'])).

thf('185',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['103','184'])).

thf('186',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('188',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['186','191'])).

thf('193',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['185','192'])).

thf('194',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('197',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('198',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
       != ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 ) )
       != ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 ) )
       != ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['195','205'])).

thf('207',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('211',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('214',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('215',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('216',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('220',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['206','212','213','216','217','218','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('222',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('223',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('224',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('225',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['222','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['221','226'])).

thf('228',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_A ) )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['220','227'])).

thf('229',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['194','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.obVydL05N8
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.19/8.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.19/8.45  % Solved by: fo/fo7.sh
% 8.19/8.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.19/8.45  % done 7489 iterations in 7.989s
% 8.19/8.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.19/8.45  % SZS output start Refutation
% 8.19/8.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.19/8.45  thf(sk_B_type, type, sk_B: $i).
% 8.19/8.45  thf(sk_C_type, type, sk_C: $i).
% 8.19/8.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.19/8.45  thf(sk_A_type, type, sk_A: $i).
% 8.19/8.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.19/8.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.19/8.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.19/8.45  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 8.19/8.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.19/8.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 8.19/8.45  thf(t50_zfmisc_1, conjecture,
% 8.19/8.45    (![A:$i,B:$i,C:$i]:
% 8.19/8.45     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 8.19/8.45  thf(zf_stmt_0, negated_conjecture,
% 8.19/8.45    (~( ![A:$i,B:$i,C:$i]:
% 8.19/8.45        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 8.19/8.45    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 8.19/8.45  thf('0', plain,
% 8.19/8.45      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.19/8.45  thf('1', plain,
% 8.19/8.45      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.19/8.45  thf(t46_xboole_1, axiom,
% 8.19/8.45    (![A:$i,B:$i]:
% 8.19/8.45     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 8.19/8.45  thf('2', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('3', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['1', '2'])).
% 8.19/8.45  thf(t42_xboole_1, axiom,
% 8.19/8.45    (![A:$i,B:$i,C:$i]:
% 8.19/8.45     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 8.19/8.45       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.19/8.45  thf('4', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('5', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['3', '4'])).
% 8.19/8.45  thf(t39_xboole_1, axiom,
% 8.19/8.45    (![A:$i,B:$i]:
% 8.19/8.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.19/8.45  thf('6', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('7', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.45           k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['5', '6'])).
% 8.19/8.45  thf('8', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ sk_C))),
% 8.19/8.45      inference('sup+', [status(thm)], ['0', '7'])).
% 8.19/8.45  thf('9', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['1', '2'])).
% 8.19/8.45  thf(t41_enumset1, axiom,
% 8.19/8.45    (![A:$i,B:$i]:
% 8.19/8.45     ( ( k2_tarski @ A @ B ) =
% 8.19/8.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 8.19/8.45  thf('10', plain,
% 8.19/8.45      (![X14 : $i, X15 : $i]:
% 8.19/8.45         ((k2_tarski @ X14 @ X15)
% 8.19/8.45           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.45  thf('11', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('12', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['1', '2'])).
% 8.19/8.45  thf('13', plain,
% 8.19/8.45      (![X14 : $i, X15 : $i]:
% 8.19/8.45         ((k2_tarski @ X14 @ X15)
% 8.19/8.45           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.45  thf('14', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('15', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('16', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['14', '15'])).
% 8.19/8.45  thf('17', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X2) @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['13', '16'])).
% 8.19/8.45  thf('18', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) @ 
% 8.19/8.45         k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['12', '17'])).
% 8.19/8.45  thf('19', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('20', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) @ X0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['18', '19'])).
% 8.19/8.45  thf('21', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('22', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) @ X0) @ 
% 8.19/8.45           k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['20', '21'])).
% 8.19/8.45  thf('23', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ k1_xboole_0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['11', '22'])).
% 8.19/8.45  thf('24', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('25', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ k1_xboole_0) @ 
% 8.19/8.45           k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['23', '24'])).
% 8.19/8.45  thf('26', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['10', '25'])).
% 8.19/8.45  thf('27', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['9', '26'])).
% 8.19/8.45  thf('28', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('29', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('30', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('31', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 8.19/8.45              k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['29', '30'])).
% 8.19/8.45  thf(t32_xboole_1, axiom,
% 8.19/8.45    (![A:$i,B:$i]:
% 8.19/8.45     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 8.19/8.45       ( ( A ) = ( B ) ) ))).
% 8.19/8.45  thf('32', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.45  thf('33', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X1))
% 8.19/8.45            != (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 8.19/8.45                k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X2 @ X1)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['31', '32'])).
% 8.19/8.45  thf('34', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k1_xboole_0)
% 8.19/8.45            != (k2_xboole_0 @ 
% 8.19/8.45                (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 8.19/8.45                 (k2_xboole_0 @ X1 @ X0)) @ 
% 8.19/8.45                k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['28', '33'])).
% 8.19/8.45  thf('35', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('36', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('37', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('38', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['36', '37'])).
% 8.19/8.45  thf('39', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('40', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('41', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('42', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.45  thf('43', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['39', '42'])).
% 8.19/8.45  thf('44', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.45  thf('45', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X1))
% 8.19/8.45            != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X1 @ X1)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['43', '44'])).
% 8.19/8.45  thf('46', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 8.19/8.45            (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))
% 8.19/8.45            != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 8.19/8.45                 (k2_xboole_0 @ X0 @ X1))))),
% 8.19/8.45      inference('sup-', [status(thm)], ['38', '45'])).
% 8.19/8.45  thf('47', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.45  thf('48', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('49', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['14', '15'])).
% 8.19/8.45  thf('50', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) @ 
% 8.19/8.45           k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['48', '49'])).
% 8.19/8.45  thf('51', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('52', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['50', '51'])).
% 8.19/8.45  thf('53', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45            != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 8.19/8.45                 (k2_xboole_0 @ X0 @ X1))))),
% 8.19/8.45      inference('demod', [status(thm)], ['46', '47', '52'])).
% 8.19/8.45  thf('54', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('simplify', [status(thm)], ['53'])).
% 8.19/8.45  thf('55', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 8.19/8.45              (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['35', '54'])).
% 8.19/8.45  thf('56', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('57', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('58', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('59', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('simplify', [status(thm)], ['53'])).
% 8.19/8.45  thf('60', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k4_xboole_0 @ 
% 8.19/8.45              (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ k1_xboole_0) @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 8.19/8.45  thf('61', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k1_xboole_0)
% 8.19/8.45            != (k4_xboole_0 @ 
% 8.19/8.45                (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 8.19/8.45                (k2_xboole_0 @ X1 @ X0)))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 8.19/8.45      inference('demod', [status(thm)], ['34', '60'])).
% 8.19/8.45  thf('62', plain,
% 8.19/8.45      ((((k1_xboole_0)
% 8.19/8.45          != (k4_xboole_0 @ 
% 8.19/8.45              (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45               k1_xboole_0) @ 
% 8.19/8.45              (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B))))
% 8.19/8.45        | ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B))
% 8.19/8.45            = (k2_xboole_0 @ 
% 8.19/8.45               (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) @ k1_xboole_0)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['27', '61'])).
% 8.19/8.45  thf('63', plain,
% 8.19/8.45      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.19/8.45  thf('64', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['14', '15'])).
% 8.19/8.45  thf('65', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.45           (k4_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['63', '64'])).
% 8.19/8.45  thf('66', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('67', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 8.19/8.45              (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['65', '66'])).
% 8.19/8.45  thf('68', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('69', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['1', '2'])).
% 8.19/8.45  thf('70', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('71', plain,
% 8.19/8.45      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['69', '70'])).
% 8.19/8.45  thf('72', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 8.19/8.45           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['67', '68', '71'])).
% 8.19/8.45  thf('73', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['9', '26'])).
% 8.19/8.45  thf('74', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['9', '26'])).
% 8.19/8.45  thf('75', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['9', '26'])).
% 8.19/8.45  thf('76', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 8.19/8.45           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['67', '68', '71'])).
% 8.19/8.45  thf('77', plain,
% 8.19/8.45      ((((k1_xboole_0)
% 8.19/8.45          != (k4_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45               k1_xboole_0) @ 
% 8.19/8.45              (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 8.19/8.45        | ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45            = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45               k1_xboole_0)))),
% 8.19/8.45      inference('demod', [status(thm)], ['62', '72', '73', '74', '75', '76'])).
% 8.19/8.45  thf(t43_enumset1, axiom,
% 8.19/8.45    (![A:$i,B:$i,C:$i]:
% 8.19/8.45     ( ( k1_enumset1 @ A @ B @ C ) =
% 8.19/8.45       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 8.19/8.45  thf('78', plain,
% 8.19/8.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.19/8.45         ((k1_enumset1 @ X16 @ X17 @ X18)
% 8.19/8.45           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t43_enumset1])).
% 8.19/8.45  thf('79', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['36', '37'])).
% 8.19/8.45  thf('80', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.19/8.45              (k2_tarski @ X2 @ X1)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['78', '79'])).
% 8.19/8.45  thf('81', plain,
% 8.19/8.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.19/8.45         ((k1_enumset1 @ X16 @ X17 @ X18)
% 8.19/8.45           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t43_enumset1])).
% 8.19/8.45  thf('82', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.19/8.45              (k2_tarski @ X2 @ X1)))),
% 8.19/8.45      inference('demod', [status(thm)], ['80', '81'])).
% 8.19/8.45  thf(l57_enumset1, axiom,
% 8.19/8.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.19/8.45     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 8.19/8.45       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 8.19/8.45  thf('83', plain,
% 8.19/8.45      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.19/8.45         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 8.19/8.45           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 8.19/8.45              (k2_tarski @ X12 @ X13)))),
% 8.19/8.45      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.19/8.45  thf('84', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.45           = (k3_enumset1 @ X2 @ X1 @ X0 @ X2 @ X1))),
% 8.19/8.45      inference('demod', [status(thm)], ['82', '83'])).
% 8.19/8.45  thf(t73_enumset1, axiom,
% 8.19/8.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.19/8.45     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 8.19/8.45       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 8.19/8.45  thf('85', plain,
% 8.19/8.45      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 8.19/8.45         ((k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29)
% 8.19/8.45           = (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 8.19/8.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.19/8.45  thf(t51_enumset1, axiom,
% 8.19/8.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.19/8.45     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 8.19/8.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 8.19/8.45  thf('86', plain,
% 8.19/8.45      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 8.19/8.45         ((k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 8.19/8.45           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 8.19/8.45              (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t51_enumset1])).
% 8.19/8.45  thf('87', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['39', '42'])).
% 8.19/8.45  thf('88', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X5)) @ 
% 8.19/8.45           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['86', '87'])).
% 8.19/8.45  thf('89', plain,
% 8.19/8.45      (![X14 : $i, X15 : $i]:
% 8.19/8.45         ((k2_tarski @ X14 @ X15)
% 8.19/8.45           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.45  thf('90', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_tarski @ X5 @ X5) @ 
% 8.19/8.45           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('demod', [status(thm)], ['88', '89'])).
% 8.19/8.45  thf('91', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_tarski @ X4 @ X4) @ 
% 8.19/8.45           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['85', '90'])).
% 8.19/8.45  thf('92', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_tarski @ X2 @ X2) @ 
% 8.19/8.45           (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ k1_xboole_0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['84', '91'])).
% 8.19/8.45  thf('93', plain,
% 8.19/8.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.19/8.45         ((k1_enumset1 @ X16 @ X17 @ X18)
% 8.19/8.45           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t43_enumset1])).
% 8.19/8.45  thf('94', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) @ 
% 8.19/8.45           k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['48', '49'])).
% 8.19/8.45  thf('95', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 8.19/8.45            (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)) @ 
% 8.19/8.45           k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['93', '94'])).
% 8.19/8.45  thf('96', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.45         = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['92', '95'])).
% 8.19/8.45  thf('97', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.45         = (k2_xboole_0 @ k1_xboole_0 @ sk_C))),
% 8.19/8.45      inference('sup+', [status(thm)], ['0', '7'])).
% 8.19/8.45  thf('98', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('99', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.45         = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['97', '98'])).
% 8.19/8.45  thf('100', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.45         = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['92', '95'])).
% 8.19/8.45  thf('101', plain,
% 8.19/8.45      ((((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.45        | ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.19/8.45      inference('demod', [status(thm)], ['77', '96', '99', '100'])).
% 8.19/8.45  thf('102', plain,
% 8.19/8.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.45      inference('simplify', [status(thm)], ['101'])).
% 8.19/8.45  thf('103', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_C))),
% 8.19/8.45      inference('demod', [status(thm)], ['8', '102'])).
% 8.19/8.45  thf('104', plain,
% 8.19/8.45      (![X2 : $i, X3 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.45           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.45  thf('105', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.45           k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['5', '6'])).
% 8.19/8.45  thf('106', plain,
% 8.19/8.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.45  thf('107', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ X1) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 8.19/8.45              (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['105', '106'])).
% 8.19/8.45  thf('108', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1) @ X0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 8.19/8.45              (k4_xboole_0 @ 
% 8.19/8.45               (k4_xboole_0 @ X0 @ 
% 8.19/8.45                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)) @ 
% 8.19/8.45               k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['104', '107'])).
% 8.19/8.45  thf('109', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ X1) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 8.19/8.45              (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['105', '106'])).
% 8.19/8.45  thf('110', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 8.19/8.45           (k4_xboole_0 @ X0 @ k1_xboole_0))
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 8.19/8.45              (k4_xboole_0 @ 
% 8.19/8.45               (k4_xboole_0 @ X0 @ 
% 8.19/8.45                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)) @ 
% 8.19/8.45               k1_xboole_0)))),
% 8.19/8.45      inference('demod', [status(thm)], ['108', '109'])).
% 8.19/8.45  thf('111', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('112', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['39', '42'])).
% 8.19/8.45  thf('113', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k4_xboole_0 @ 
% 8.19/8.45              (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ k1_xboole_0) @ X0))),
% 8.19/8.45      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 8.19/8.45  thf('114', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45           k1_xboole_0)
% 8.19/8.45           = (k4_xboole_0 @ 
% 8.19/8.45              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ k1_xboole_0) @ 
% 8.19/8.45              (k2_xboole_0 @ X1 @ X0)))),
% 8.19/8.45      inference('sup+', [status(thm)], ['112', '113'])).
% 8.19/8.45  thf('115', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.45  thf('116', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 8.19/8.45            (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ k1_xboole_0))
% 8.19/8.45            != (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45                k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ k1_xboole_0)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['114', '115'])).
% 8.19/8.45  thf('117', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         (((k1_xboole_0)
% 8.19/8.45            != (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.45                k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['111', '116'])).
% 8.19/8.45  thf('118', plain,
% 8.19/8.45      (((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.45         = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['92', '95'])).
% 8.19/8.45  thf('119', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.45  thf('120', plain,
% 8.19/8.45      ((((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.45          != (k1_xboole_0))
% 8.19/8.45        | ((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['118', '119'])).
% 8.19/8.45  thf('121', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('122', plain,
% 8.19/8.45      ((((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.45        | ((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.19/8.45      inference('demod', [status(thm)], ['120', '121'])).
% 8.19/8.45  thf('123', plain,
% 8.19/8.45      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.45  thf('124', plain,
% 8.19/8.45      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.45  thf('125', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         (((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.45              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)))),
% 8.19/8.45      inference('demod', [status(thm)], ['117', '123', '124'])).
% 8.19/8.45  thf('126', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 8.19/8.45      inference('simplify', [status(thm)], ['125'])).
% 8.19/8.45  thf('127', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('simplify', [status(thm)], ['53'])).
% 8.19/8.45  thf('128', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 8.19/8.45      inference('simplify', [status(thm)], ['125'])).
% 8.19/8.45  thf('129', plain,
% 8.19/8.45      (![X7 : $i, X8 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.45  thf('130', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 8.19/8.45           = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['128', '129'])).
% 8.19/8.45  thf('131', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 8.19/8.45           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 8.19/8.45           = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['127', '130'])).
% 8.19/8.45  thf('132', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('simplify', [status(thm)], ['53'])).
% 8.19/8.45  thf('133', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.45  thf('134', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45            (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)))
% 8.19/8.45           = (k1_xboole_0))),
% 8.19/8.45      inference('demod', [status(thm)], ['131', '132', '133'])).
% 8.19/8.45  thf('135', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         ((k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45           (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))
% 8.19/8.45           = (k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['126', '134'])).
% 8.19/8.45  thf('136', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.45      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.45  thf('137', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.45      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.45  thf('138', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2))
% 8.19/8.45            != (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.45                (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 8.19/8.45          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X1 @ X2)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['136', '137'])).
% 8.19/8.45  thf('139', plain,
% 8.19/8.45      (![X0 : $i]:
% 8.19/8.45         (((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ 
% 8.19/8.45            (k2_xboole_0 @ X0 @ k1_xboole_0)) != (k1_xboole_0))
% 8.19/8.45          | ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.45      inference('sup-', [status(thm)], ['135', '138'])).
% 8.19/8.45  thf('140', plain,
% 8.19/8.45      (![X0 : $i, X1 : $i]:
% 8.19/8.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.45           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.45      inference('sup+', [status(thm)], ['39', '42'])).
% 8.19/8.46  thf('141', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('142', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.46           = (k1_xboole_0))),
% 8.19/8.46      inference('demod', [status(thm)], ['140', '141'])).
% 8.19/8.46  thf('143', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.46          | ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.46      inference('demod', [status(thm)], ['139', '142'])).
% 8.19/8.46  thf('144', plain,
% 8.19/8.46      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['143'])).
% 8.19/8.46  thf('145', plain,
% 8.19/8.46      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['143'])).
% 8.19/8.46  thf('146', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['125'])).
% 8.19/8.46  thf('147', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['145', '146'])).
% 8.19/8.46  thf('148', plain,
% 8.19/8.46      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['143'])).
% 8.19/8.46  thf('149', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['147', '148'])).
% 8.19/8.46  thf('150', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['144', '149'])).
% 8.19/8.46  thf('151', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.46      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.46  thf('152', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['147', '148'])).
% 8.19/8.46  thf('153', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2))
% 8.19/8.46            != (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46                (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 8.19/8.46          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X1 @ X2)))),
% 8.19/8.46      inference('sup-', [status(thm)], ['136', '137'])).
% 8.19/8.46  thf('154', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 8.19/8.46            (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))
% 8.19/8.46            != (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46                (k4_xboole_0 @ X1 @ 
% 8.19/8.46                 (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))))
% 8.19/8.46          | ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)))),
% 8.19/8.46      inference('sup-', [status(thm)], ['152', '153'])).
% 8.19/8.46  thf('155', plain,
% 8.19/8.46      (![X7 : $i, X8 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.46      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.46  thf('156', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['147', '148'])).
% 8.19/8.46  thf('157', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['147', '148'])).
% 8.19/8.46  thf('158', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((k1_xboole_0)
% 8.19/8.46            != (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46                (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))))
% 8.19/8.46          | ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)))),
% 8.19/8.46      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 8.19/8.46  thf('159', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((k1_xboole_0)
% 8.19/8.46            != (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 8.19/8.46                (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 8.19/8.46          | ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)))),
% 8.19/8.46      inference('sup-', [status(thm)], ['151', '158'])).
% 8.19/8.46  thf('160', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((k1_xboole_0)
% 8.19/8.46            != (k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1) @ 
% 8.19/8.46                (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 8.19/8.46          | ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ 
% 8.19/8.46                 (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0) @ X1)))),
% 8.19/8.46      inference('sup-', [status(thm)], ['150', '159'])).
% 8.19/8.46  thf('161', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['144', '149'])).
% 8.19/8.46  thf('162', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['144', '149'])).
% 8.19/8.46  thf('163', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((k1_xboole_0)
% 8.19/8.46            != (k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1) @ 
% 8.19/8.46                (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 8.19/8.46          | ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)))),
% 8.19/8.46      inference('demod', [status(thm)], ['160', '161', '162'])).
% 8.19/8.46  thf('164', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k1_xboole_0)
% 8.19/8.46            != (k4_xboole_0 @ 
% 8.19/8.46                (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.46                 (k4_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 8.19/8.46                (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 8.19/8.46          | ((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 8.19/8.46                 (k4_xboole_0 @ 
% 8.19/8.46                  (k4_xboole_0 @ X0 @ 
% 8.19/8.46                   (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)) @ 
% 8.19/8.46                  k1_xboole_0))))),
% 8.19/8.46      inference('sup-', [status(thm)], ['110', '163'])).
% 8.19/8.46  thf('165', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('166', plain,
% 8.19/8.46      (![X2 : $i, X3 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.46           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.46  thf('167', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('168', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('169', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.19/8.46      inference('sup+', [status(thm)], ['40', '41'])).
% 8.19/8.46  thf('170', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 8.19/8.46           (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.19/8.46      inference('sup+', [status(thm)], ['168', '169'])).
% 8.19/8.46  thf('171', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('172', plain,
% 8.19/8.46      (![X2 : $i, X3 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.46           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.46  thf('173', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.46      inference('demod', [status(thm)], ['170', '171', '172'])).
% 8.19/8.46  thf('174', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('175', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('176', plain,
% 8.19/8.46      (![X14 : $i, X15 : $i]:
% 8.19/8.46         ((k2_tarski @ X14 @ X15)
% 8.19/8.46           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.46  thf('177', plain,
% 8.19/8.46      (![X7 : $i, X8 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.46      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.46  thf('178', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 8.19/8.46           = (k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['176', '177'])).
% 8.19/8.46  thf('179', plain,
% 8.19/8.46      (![X2 : $i, X3 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.46           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.46  thf('180', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))),
% 8.19/8.46      inference('sup+', [status(thm)], ['178', '179'])).
% 8.19/8.46  thf('181', plain,
% 8.19/8.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.19/8.46         ((k1_enumset1 @ X16 @ X17 @ X18)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t43_enumset1])).
% 8.19/8.46  thf('182', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k1_enumset1 @ X0 @ X1 @ X0))),
% 8.19/8.46      inference('demod', [status(thm)], ['180', '181'])).
% 8.19/8.46  thf('183', plain,
% 8.19/8.46      (![X2 : $i, X3 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 8.19/8.46           = (k2_xboole_0 @ X2 @ X3))),
% 8.19/8.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.19/8.46  thf('184', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ X0))
% 8.19/8.46          | ((k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46                 (k4_xboole_0 @ X0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A)))))),
% 8.19/8.46      inference('demod', [status(thm)],
% 8.19/8.46                ['164', '165', '166', '167', '173', '174', '175', '182', '183'])).
% 8.19/8.46  thf('185', plain,
% 8.19/8.46      ((((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.46        | ((k1_xboole_0)
% 8.19/8.46            = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46               (k4_xboole_0 @ sk_C @ (k1_enumset1 @ sk_A @ sk_B @ sk_A)))))),
% 8.19/8.46      inference('sup-', [status(thm)], ['103', '184'])).
% 8.19/8.46  thf('186', plain,
% 8.19/8.46      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.19/8.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.19/8.46  thf('187', plain,
% 8.19/8.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.19/8.46         ((k1_enumset1 @ X16 @ X17 @ X18)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t43_enumset1])).
% 8.19/8.46  thf('188', plain,
% 8.19/8.46      (![X7 : $i, X8 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 8.19/8.46      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.19/8.46  thf('189', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 8.19/8.46           = (k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['187', '188'])).
% 8.19/8.46  thf('190', plain,
% 8.19/8.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.46  thf('191', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X3) @ 
% 8.19/8.46           (k1_enumset1 @ X2 @ X1 @ X0))
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46              (k4_xboole_0 @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 8.19/8.46      inference('sup+', [status(thm)], ['189', '190'])).
% 8.19/8.46  thf('192', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ X0))
% 8.19/8.46           = (k2_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46              (k4_xboole_0 @ sk_C @ (k1_enumset1 @ sk_A @ sk_B @ X0))))),
% 8.19/8.46      inference('sup+', [status(thm)], ['186', '191'])).
% 8.19/8.46  thf('193', plain,
% 8.19/8.46      ((((k1_xboole_0) != (k1_xboole_0))
% 8.19/8.46        | ((k1_xboole_0)
% 8.19/8.46            = (k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A))))),
% 8.19/8.46      inference('demod', [status(thm)], ['185', '192'])).
% 8.19/8.46  thf('194', plain,
% 8.19/8.46      (((k1_xboole_0)
% 8.19/8.46         = (k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A)))),
% 8.19/8.46      inference('simplify', [status(thm)], ['193'])).
% 8.19/8.46  thf('195', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ X0 @ X0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['125'])).
% 8.19/8.46  thf('196', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['36', '37'])).
% 8.19/8.46  thf('197', plain,
% 8.19/8.46      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['1', '2'])).
% 8.19/8.46  thf('198', plain,
% 8.19/8.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 8.19/8.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t42_xboole_1])).
% 8.19/8.46  thf('199', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 8.19/8.46           k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['197', '198'])).
% 8.19/8.46  thf('200', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         (((X1) = (X0)) | ((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X0 @ X1)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t32_xboole_1])).
% 8.19/8.46  thf('201', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k4_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46            (k2_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 8.19/8.46            != (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))
% 8.19/8.46          | ((k1_xboole_0) = (k2_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))))),
% 8.19/8.46      inference('sup-', [status(thm)], ['199', '200'])).
% 8.19/8.46  thf('202', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k4_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.46             k1_xboole_0))
% 8.19/8.46            != (k2_xboole_0 @ 
% 8.19/8.46                (k4_xboole_0 @ 
% 8.19/8.46                 (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ k1_xboole_0) @ 
% 8.19/8.46                k1_xboole_0))
% 8.19/8.46          | ((k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ 
% 8.19/8.46                 (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.46                 (k2_tarski @ sk_A @ sk_B))))),
% 8.19/8.46      inference('sup-', [status(thm)], ['196', '201'])).
% 8.19/8.46  thf('203', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.46           k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.19/8.46      inference('demod', [status(thm)], ['5', '6'])).
% 8.19/8.46  thf('204', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.19/8.46      inference('sup+', [status(thm)], ['36', '37'])).
% 8.19/8.46  thf('205', plain,
% 8.19/8.46      (![X0 : $i]:
% 8.19/8.46         (((k4_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 8.19/8.46             k1_xboole_0))
% 8.19/8.46            != (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))
% 8.19/8.46          | ((k1_xboole_0)
% 8.19/8.46              = (k2_xboole_0 @ 
% 8.19/8.46                 (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ k1_xboole_0)))),
% 8.19/8.46      inference('demod', [status(thm)], ['202', '203', '204'])).
% 8.19/8.46  thf('206', plain,
% 8.19/8.46      ((((k4_xboole_0 @ k1_xboole_0 @ 
% 8.19/8.46          (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B)))
% 8.19/8.46          != (k2_xboole_0 @ 
% 8.19/8.46              (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 8.19/8.46              k1_xboole_0))
% 8.19/8.46        | ((k1_xboole_0)
% 8.19/8.46            = (k2_xboole_0 @ 
% 8.19/8.46               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 8.19/8.46                (k2_tarski @ sk_A @ sk_B)) @ 
% 8.19/8.46               k1_xboole_0)))),
% 8.19/8.46      inference('sup-', [status(thm)], ['195', '205'])).
% 8.19/8.46  thf('207', plain,
% 8.19/8.46      (![X14 : $i, X15 : $i]:
% 8.19/8.46         ((k2_tarski @ X14 @ X15)
% 8.19/8.46           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.46  thf('208', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 8.19/8.46      inference('simplify', [status(thm)], ['53'])).
% 8.19/8.46  thf('209', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 8.19/8.46           k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.19/8.46              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 8.19/8.46      inference('sup+', [status(thm)], ['207', '208'])).
% 8.19/8.46  thf('210', plain,
% 8.19/8.46      (![X14 : $i, X15 : $i]:
% 8.19/8.46         ((k2_tarski @ X14 @ X15)
% 8.19/8.46           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.46  thf('211', plain,
% 8.19/8.46      (![X14 : $i, X15 : $i]:
% 8.19/8.46         ((k2_tarski @ X14 @ X15)
% 8.19/8.46           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.19/8.46  thf('212', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0)))),
% 8.19/8.46      inference('demod', [status(thm)], ['209', '210', '211'])).
% 8.19/8.46  thf('213', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k1_enumset1 @ X0 @ X1 @ X0))),
% 8.19/8.46      inference('demod', [status(thm)], ['180', '181'])).
% 8.19/8.46  thf('214', plain,
% 8.19/8.46      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 8.19/8.46         = (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 8.19/8.46      inference('sup+', [status(thm)], ['69', '70'])).
% 8.19/8.46  thf('215', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('216', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 8.19/8.46      inference('demod', [status(thm)], ['214', '215'])).
% 8.19/8.46  thf('217', plain,
% 8.19/8.46      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 8.19/8.46      inference('simplify', [status(thm)], ['122'])).
% 8.19/8.46  thf('218', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0)))),
% 8.19/8.46      inference('demod', [status(thm)], ['209', '210', '211'])).
% 8.19/8.46  thf('219', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 8.19/8.46           = (k1_enumset1 @ X0 @ X1 @ X0))),
% 8.19/8.46      inference('demod', [status(thm)], ['180', '181'])).
% 8.19/8.46  thf('220', plain,
% 8.19/8.46      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A))
% 8.19/8.46          != (k1_xboole_0))
% 8.19/8.46        | ((k1_xboole_0)
% 8.19/8.46            = (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A) @ k1_xboole_0)))),
% 8.19/8.46      inference('demod', [status(thm)],
% 8.19/8.46                ['206', '212', '213', '216', '217', '218', '219'])).
% 8.19/8.46  thf('221', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.46           = (k3_enumset1 @ X2 @ X1 @ X0 @ X2 @ X1))),
% 8.19/8.46      inference('demod', [status(thm)], ['82', '83'])).
% 8.19/8.46  thf('222', plain,
% 8.19/8.46      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 8.19/8.46         ((k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29)
% 8.19/8.46           = (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 8.19/8.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.19/8.46  thf('223', plain,
% 8.19/8.46      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 8.19/8.46         ((k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 8.19/8.46           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 8.19/8.46              (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)))),
% 8.19/8.46      inference('cnf', [status(esa)], [t51_enumset1])).
% 8.19/8.46  thf(t49_zfmisc_1, axiom,
% 8.19/8.46    (![A:$i,B:$i]:
% 8.19/8.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 8.19/8.46  thf('224', plain,
% 8.19/8.46      (![X36 : $i, X37 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k1_tarski @ X36) @ X37) != (k1_xboole_0))),
% 8.19/8.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 8.19/8.46  thf('225', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.19/8.46         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.19/8.46      inference('sup-', [status(thm)], ['223', '224'])).
% 8.19/8.46  thf('226', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.19/8.46         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.19/8.46      inference('sup-', [status(thm)], ['222', '225'])).
% 8.19/8.46  thf('227', plain,
% 8.19/8.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.19/8.46         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ k1_xboole_0)
% 8.19/8.46           != (k1_xboole_0))),
% 8.19/8.46      inference('sup-', [status(thm)], ['221', '226'])).
% 8.19/8.46  thf('228', plain,
% 8.19/8.46      (((k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_A))
% 8.19/8.46         != (k1_xboole_0))),
% 8.19/8.46      inference('simplify_reflect-', [status(thm)], ['220', '227'])).
% 8.19/8.46  thf('229', plain, ($false),
% 8.19/8.46      inference('simplify_reflect-', [status(thm)], ['194', '228'])).
% 8.19/8.46  
% 8.19/8.46  % SZS output end Refutation
% 8.19/8.46  
% 8.19/8.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
