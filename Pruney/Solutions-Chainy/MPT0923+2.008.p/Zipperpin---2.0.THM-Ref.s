%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SoTmZa5Mow

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 330 expanded)
%              Number of leaves         :   24 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  940 (3799 expanded)
%              Number of equality atoms :   69 ( 230 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t83_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
        & ! [F: $i,G: $i,H: $i,I: $i] :
            ~ ( ( r2_hidden @ F @ B )
              & ( r2_hidden @ G @ C )
              & ( r2_hidden @ H @ D )
              & ( r2_hidden @ I @ E )
              & ( A
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
          & ! [F: $i,G: $i,H: $i,I: $i] :
              ~ ( ( r2_hidden @ F @ B )
                & ( r2_hidden @ G @ C )
                & ( r2_hidden @ H @ D )
                & ( r2_hidden @ I @ E )
                & ( A
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X4 ) @ ( sk_E @ X4 ) )
        = X4 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('10',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('27',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X17 @ X18 ) @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('44',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('50',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 )
      = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('61',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ~ ( r2_hidden @ X25 @ sk_C )
      | ~ ( r2_hidden @ X26 @ sk_D_1 )
      | ( sk_A
       != ( k4_mcart_1 @ X24 @ X25 @ X26 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ( sk_A
       != ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','68'])).

thf('70',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['12','75'])).

thf('77',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_1 ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    $false ),
    inference(simplify,[status(thm)],['82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SoTmZa5Mow
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 81 iterations in 0.045s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(t83_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.21/0.51          ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.21/0.51                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.21/0.51                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.21/0.51             ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.51               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.21/0.51                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.21/0.51                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d4_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf(l139_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.51          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51          | ((k4_tarski @ (sk_D @ X4) @ (sk_E @ X4)) = (X4)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf('5', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf(t7_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '7'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('11', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf(t10_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.51         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf(d3_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.51          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_D @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((k2_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_E @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '28'])).
% 0.21/0.51  thf(t31_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X17 @ X18) @ X19) @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf(d4_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.51           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.21/0.51           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.21/0.51         = (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.21/0.51         = (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51         (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.21/0.51           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.21/0.51      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.51           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.21/0.51           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.21/0.51      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0)
% 0.21/0.51           = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51              (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['52', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X24 @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ X25 @ sk_C)
% 0.21/0.51          | ~ (r2_hidden @ X26 @ sk_D_1)
% 0.21/0.51          | ((sk_A) != (k4_mcart_1 @ X24 @ X25 @ X26 @ X27))
% 0.21/0.51          | ~ (r2_hidden @ X27 @ sk_E_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ sk_E_1)
% 0.21/0.51          | ((sk_A)
% 0.21/0.51              != (k4_mcart_1 @ 
% 0.21/0.51                  (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X2 @ 
% 0.21/0.51                  X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.21/0.51          | ~ (r2_hidden @ X2 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((sk_A)
% 0.21/0.51            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51               sk_C)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X14) @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((sk_A)
% 0.21/0.51            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E_1)
% 0.21/0.51          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X14) @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['69', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X14) @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['77', '80'])).
% 0.21/0.51  thf('82', plain, (((sk_A) != (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['76', '81'])).
% 0.21/0.51  thf('83', plain, ($false), inference('simplify', [status(thm)], ['82'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
