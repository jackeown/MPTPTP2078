%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0MynRoIEgG

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:02 EST 2020

% Result     : Theorem 54.62s
% Output     : Refutation 54.62s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 196 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  832 (1687 expanded)
%              Number of equality atoms :   47 ( 107 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ X19 @ ( k2_xboole_0 @ X16 @ X18 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X19 @ X16 ) @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X1 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['16','17','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['35','71','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0MynRoIEgG
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:18:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 54.62/54.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.62/54.83  % Solved by: fo/fo7.sh
% 54.62/54.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.62/54.83  % done 26831 iterations in 54.388s
% 54.62/54.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.62/54.83  % SZS output start Refutation
% 54.62/54.83  thf(sk_B_type, type, sk_B: $i).
% 54.62/54.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 54.62/54.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.62/54.83  thf(sk_D_type, type, sk_D: $i).
% 54.62/54.83  thf(sk_F_type, type, sk_F: $i).
% 54.62/54.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 54.62/54.83  thf(sk_E_type, type, sk_E: $i).
% 54.62/54.83  thf(sk_A_type, type, sk_A: $i).
% 54.62/54.83  thf(sk_C_type, type, sk_C: $i).
% 54.62/54.83  thf(t143_zfmisc_1, conjecture,
% 54.62/54.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 54.62/54.83     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 54.62/54.83         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 54.62/54.83       ( r1_tarski @
% 54.62/54.83         ( k2_xboole_0 @ A @ B ) @ 
% 54.62/54.83         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 54.62/54.83  thf(zf_stmt_0, negated_conjecture,
% 54.62/54.83    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 54.62/54.83        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 54.62/54.83            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 54.62/54.83          ( r1_tarski @
% 54.62/54.83            ( k2_xboole_0 @ A @ B ) @ 
% 54.62/54.83            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 54.62/54.83    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 54.62/54.83  thf('0', plain,
% 54.62/54.83      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 54.62/54.83          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 54.62/54.83           (k2_xboole_0 @ sk_D @ sk_F)))),
% 54.62/54.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.62/54.83  thf(t120_zfmisc_1, axiom,
% 54.62/54.83    (![A:$i,B:$i,C:$i]:
% 54.62/54.83     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 54.62/54.83         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 54.62/54.83       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 54.62/54.83         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 54.62/54.83  thf('1', plain,
% 54.62/54.83      (![X16 : $i, X18 : $i, X19 : $i]:
% 54.62/54.83         ((k2_zfmisc_1 @ X19 @ (k2_xboole_0 @ X16 @ X18))
% 54.62/54.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X19 @ X16) @ 
% 54.62/54.83              (k2_zfmisc_1 @ X19 @ X18)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 54.62/54.83  thf('2', plain,
% 54.62/54.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 54.62/54.83         ((k2_zfmisc_1 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 54.62/54.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 54.62/54.83              (k2_zfmisc_1 @ X18 @ X17)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 54.62/54.83  thf(commutativity_k2_xboole_0, axiom,
% 54.62/54.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 54.62/54.83  thf('3', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf(t7_xboole_1, axiom,
% 54.62/54.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 54.62/54.83  thf('4', plain,
% 54.62/54.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 54.62/54.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 54.62/54.83  thf('5', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['3', '4'])).
% 54.62/54.83  thf('6', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 54.62/54.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.62/54.83  thf(t12_xboole_1, axiom,
% 54.62/54.83    (![A:$i,B:$i]:
% 54.62/54.83     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 54.62/54.83  thf('7', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('8', plain,
% 54.62/54.83      (((k2_xboole_0 @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))
% 54.62/54.83         = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 54.62/54.83      inference('sup-', [status(thm)], ['6', '7'])).
% 54.62/54.83  thf(t11_xboole_1, axiom,
% 54.62/54.83    (![A:$i,B:$i,C:$i]:
% 54.62/54.83     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 54.62/54.83  thf('9', plain,
% 54.62/54.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 54.62/54.83         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 54.62/54.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 54.62/54.83  thf('10', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0)
% 54.62/54.83          | (r1_tarski @ sk_B @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['8', '9'])).
% 54.62/54.83  thf('11', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 54.62/54.83      inference('sup-', [status(thm)], ['5', '10'])).
% 54.62/54.83  thf('12', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F))),
% 54.62/54.83      inference('sup+', [status(thm)], ['2', '11'])).
% 54.62/54.83  thf('13', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 54.62/54.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.62/54.83  thf(t13_xboole_1, axiom,
% 54.62/54.83    (![A:$i,B:$i,C:$i,D:$i]:
% 54.62/54.83     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 54.62/54.83       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 54.62/54.83  thf('14', plain,
% 54.62/54.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 54.62/54.83         (~ (r1_tarski @ X7 @ X8)
% 54.62/54.83          | ~ (r1_tarski @ X9 @ X10)
% 54.62/54.83          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t13_xboole_1])).
% 54.62/54.83  thf('15', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X1) @ 
% 54.62/54.83           (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))
% 54.62/54.83          | ~ (r1_tarski @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['13', '14'])).
% 54.62/54.83  thf('16', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_B) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ 
% 54.62/54.83           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F)))),
% 54.62/54.83      inference('sup-', [status(thm)], ['12', '15'])).
% 54.62/54.83  thf('17', plain,
% 54.62/54.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 54.62/54.83         ((k2_zfmisc_1 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 54.62/54.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 54.62/54.83              (k2_zfmisc_1 @ X18 @ X17)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 54.62/54.83  thf('18', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('19', plain,
% 54.62/54.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 54.62/54.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 54.62/54.83  thf('20', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('21', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['19', '20'])).
% 54.62/54.83  thf('22', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['18', '21'])).
% 54.62/54.83  thf('23', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_B) @ 
% 54.62/54.83          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 54.62/54.83      inference('demod', [status(thm)], ['16', '17', '22'])).
% 54.62/54.83  thf('24', plain,
% 54.62/54.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 54.62/54.83         ((k2_zfmisc_1 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 54.62/54.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 54.62/54.83              (k2_zfmisc_1 @ X18 @ X17)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 54.62/54.83  thf('25', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['3', '4'])).
% 54.62/54.83  thf('26', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 54.62/54.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.62/54.83  thf('27', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('28', plain,
% 54.62/54.83      (((k2_xboole_0 @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 54.62/54.83         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 54.62/54.83      inference('sup-', [status(thm)], ['26', '27'])).
% 54.62/54.83  thf('29', plain,
% 54.62/54.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 54.62/54.83         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 54.62/54.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 54.62/54.83  thf('30', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0)
% 54.62/54.83          | (r1_tarski @ sk_A @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['28', '29'])).
% 54.62/54.83  thf('31', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 54.62/54.83      inference('sup-', [status(thm)], ['25', '30'])).
% 54.62/54.83  thf('32', plain,
% 54.62/54.83      (![X0 : $i]:
% 54.62/54.83         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 54.62/54.83      inference('sup+', [status(thm)], ['24', '31'])).
% 54.62/54.83  thf('33', plain,
% 54.62/54.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 54.62/54.83         (~ (r1_tarski @ X7 @ X8)
% 54.62/54.83          | ~ (r1_tarski @ X9 @ X10)
% 54.62/54.83          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t13_xboole_1])).
% 54.62/54.83  thf('34', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 54.62/54.83           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D) @ X1))
% 54.62/54.83          | ~ (r1_tarski @ X2 @ X1))),
% 54.62/54.83      inference('sup-', [status(thm)], ['32', '33'])).
% 54.62/54.83  thf('35', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_B)) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 54.62/54.83           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 54.62/54.83      inference('sup-', [status(thm)], ['23', '34'])).
% 54.62/54.83  thf('36', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('37', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['3', '4'])).
% 54.62/54.83  thf('38', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('39', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['37', '38'])).
% 54.62/54.83  thf('40', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['36', '39'])).
% 54.62/54.83  thf('41', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('42', plain,
% 54.62/54.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 54.62/54.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 54.62/54.83  thf(t9_xboole_1, axiom,
% 54.62/54.83    (![A:$i,B:$i,C:$i]:
% 54.62/54.83     ( ( r1_tarski @ A @ B ) =>
% 54.62/54.83       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 54.62/54.83  thf('43', plain,
% 54.62/54.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 54.62/54.83         (~ (r1_tarski @ X13 @ X14)
% 54.62/54.83          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ (k2_xboole_0 @ X14 @ X15)))),
% 54.62/54.83      inference('cnf', [status(esa)], [t9_xboole_1])).
% 54.62/54.83  thf('44', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 54.62/54.83      inference('sup-', [status(thm)], ['42', '43'])).
% 54.62/54.83  thf('45', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 54.62/54.83          (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 54.62/54.83      inference('sup+', [status(thm)], ['41', '44'])).
% 54.62/54.83  thf('46', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['40', '45'])).
% 54.62/54.83  thf('47', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('48', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['46', '47'])).
% 54.62/54.83  thf('49', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('50', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['48', '49'])).
% 54.62/54.83  thf('51', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('52', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 54.62/54.83      inference('sup-', [status(thm)], ['42', '43'])).
% 54.62/54.83  thf('53', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['51', '52'])).
% 54.62/54.83  thf('54', plain,
% 54.62/54.83      (![X5 : $i, X6 : $i]:
% 54.62/54.83         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 54.62/54.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 54.62/54.83  thf('55', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ 
% 54.62/54.83           (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['53', '54'])).
% 54.62/54.83  thf('56', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1) @ 
% 54.62/54.83           (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 54.62/54.83      inference('sup+', [status(thm)], ['50', '55'])).
% 54.62/54.83  thf('57', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('58', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ 
% 54.62/54.83           (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['53', '54'])).
% 54.62/54.83  thf('59', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['46', '47'])).
% 54.62/54.83  thf('60', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['18', '21'])).
% 54.62/54.83  thf('61', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 54.62/54.83      inference('sup+', [status(thm)], ['59', '60'])).
% 54.62/54.83  thf('62', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup-', [status(thm)], ['37', '38'])).
% 54.62/54.83  thf('63', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['18', '21'])).
% 54.62/54.83  thf('64', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['62', '63'])).
% 54.62/54.83  thf('65', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('66', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('sup+', [status(thm)], ['18', '21'])).
% 54.62/54.83  thf('67', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('demod', [status(thm)], ['64', '65', '66'])).
% 54.62/54.83  thf('68', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ X1)
% 54.62/54.83           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 54.62/54.83      inference('demod', [status(thm)], ['61', '67'])).
% 54.62/54.83  thf('69', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 54.62/54.83           = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('demod', [status(thm)], ['56', '57', '58', '68'])).
% 54.62/54.83  thf('70', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('71', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1))
% 54.62/54.83           = (k2_xboole_0 @ X1 @ X0))),
% 54.62/54.83      inference('sup+', [status(thm)], ['69', '70'])).
% 54.62/54.83  thf('72', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('73', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]:
% 54.62/54.83         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 54.62/54.83          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 54.62/54.83           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 54.62/54.83      inference('demod', [status(thm)], ['35', '71', '72'])).
% 54.62/54.83  thf('74', plain,
% 54.62/54.83      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 54.62/54.83        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C) @ 
% 54.62/54.83         (k2_xboole_0 @ sk_D @ sk_F)))),
% 54.62/54.83      inference('sup+', [status(thm)], ['1', '73'])).
% 54.62/54.83  thf('75', plain,
% 54.62/54.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 54.62/54.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 54.62/54.83  thf('76', plain,
% 54.62/54.83      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 54.62/54.83        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 54.62/54.83         (k2_xboole_0 @ sk_D @ sk_F)))),
% 54.62/54.83      inference('demod', [status(thm)], ['74', '75'])).
% 54.62/54.83  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 54.62/54.83  
% 54.62/54.83  % SZS output end Refutation
% 54.62/54.83  
% 54.65/54.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
