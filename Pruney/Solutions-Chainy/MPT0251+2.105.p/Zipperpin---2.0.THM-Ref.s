%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8rHAUQwmG

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 330 expanded)
%              Number of leaves         :   24 ( 119 expanded)
%              Depth                    :   26
%              Number of atoms          :  894 (2485 expanded)
%              Number of equality atoms :   98 ( 295 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_xboole_0 @ X49 @ ( k1_tarski @ X48 ) )
        = ( k1_tarski @ X48 ) )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('25',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('30',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('40',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('52',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['26','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('64',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('65',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('66',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','92'])).

thf('94',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['57','93'])).

thf('95',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8rHAUQwmG
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 587 iterations in 0.203s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t1_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('0', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf(t46_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.64  thf('2', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('3', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf(t21_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.46/0.64  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf(t98_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ X19)
% 0.46/0.64           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf(t46_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.64       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( r2_hidden @ A @ B ) =>
% 0.46/0.64          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.46/0.64  thf('10', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(l31_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.64       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X48 : $i, X49 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X49 @ (k1_tarski @ X48)) = (k1_tarski @ X48))
% 0.46/0.64          | ~ (r2_hidden @ X48 @ X49))),
% 0.46/0.64      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(t91_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ X0)
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.46/0.64           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['9', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.46/0.64         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['8', '17'])).
% 0.46/0.64  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (((k1_xboole_0)
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64            (k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ 
% 0.46/0.64             (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['7', '22'])).
% 0.46/0.64  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.46/0.64           (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['2', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ X19)
% 0.46/0.64           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ k1_xboole_0) @ X0)
% 0.46/0.64           = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.64           = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (((k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64         (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64          (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.46/0.64         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64            (k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ 
% 0.46/0.64             (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['29', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (((k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 0.46/0.64         = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64              (k5_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ k1_xboole_0) @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64              (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64              (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['28', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ sk_B_1 @ 
% 0.46/0.64              (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (((k4_xboole_0 @ k1_xboole_0 @ sk_B_1)
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['27', '47'])).
% 0.46/0.64  thf('49', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('52', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ X19)
% 0.46/0.64           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.46/0.64         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('56', plain, (((sk_B_1) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.46/0.64           (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.46/0.64           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.46/0.64           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['58', '61'])).
% 0.46/0.64  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.64  thf('64', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf(t4_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.46/0.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['64', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ X2 @ X3)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.46/0.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '75'])).
% 0.46/0.64  thf('77', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ X19)
% 0.46/0.64           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.64  thf('89', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '90'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['63', '91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '92'])).
% 0.46/0.64  thf('94', plain, (((sk_B_1) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['57', '93'])).
% 0.46/0.64  thf('95', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('96', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
