%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPHVPbOpxa

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:17 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 354 expanded)
%              Number of leaves         :   24 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          :  925 (4080 expanded)
%              Number of equality atoms :   67 ( 248 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

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
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X4 ) @ ( sk_E @ X4 ) )
        = X4 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','9'])).

thf('12',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('29',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('40',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('43',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('46',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_mcart_1 @ X12 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X12 @ X13 ) @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_mcart_1 @ X12 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ X15 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 )
      = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('58',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('59',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_B )
      | ~ ( r2_hidden @ X28 @ sk_C )
      | ~ ( r2_hidden @ X29 @ sk_D_1 )
      | ( sk_A
       != ( k4_mcart_1 @ X27 @ X28 @ X29 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( sk_A
       != ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('65',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','66'])).

thf('68',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['14','73'])).

thf('75',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_2 ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    $false ),
    inference(simplify,[status(thm)],['80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPHVPbOpxa
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 234 iterations in 0.118s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i > $i).
% 0.39/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i > $i).
% 0.39/0.57  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.39/0.57  thf(t83_mcart_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.39/0.57          ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.39/0.57            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.39/0.57                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.39/0.57                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.39/0.57             ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.39/0.57               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.39/0.57                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.39/0.57                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t53_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.39/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18) @ 
% 0.39/0.57              X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.39/0.57  thf(d3_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.39/0.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(l139_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.39/0.57          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.57          | ((k4_tarski @ (sk_D @ X4) @ (sk_E @ X4)) = (X4)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.57  thf('7', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.57  thf(t7_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.39/0.57       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('9', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '9'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.39/0.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(t10_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.39/0.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.39/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.57          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.57          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '22'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_D @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '26'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (((k2_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_E @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.57  thf(d3_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.39/0.57           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.57          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.39/0.57         = (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '43'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.39/0.57         = (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57         (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '47'])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.39/0.57           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.39/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf(t31_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.39/0.57       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         ((k4_mcart_1 @ X12 @ X13 @ X14 @ X15)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X12 @ X13) @ X14) @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         ((k4_mcart_1 @ X12 @ X13 @ X14 @ X15)
% 0.39/0.57           = (k4_tarski @ (k3_mcart_1 @ X12 @ X13 @ X14) @ X15))),
% 0.39/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.39/0.57           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '54'])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0)
% 0.39/0.57           = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57              (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['48', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X27 @ sk_B)
% 0.39/0.57          | ~ (r2_hidden @ X28 @ sk_C)
% 0.39/0.57          | ~ (r2_hidden @ X29 @ sk_D_1)
% 0.39/0.57          | ((sk_A) != (k4_mcart_1 @ X27 @ X28 @ X29 @ X30))
% 0.39/0.57          | ~ (r2_hidden @ X30 @ sk_E_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ sk_E_2)
% 0.39/0.57          | ((sk_A)
% 0.39/0.57              != (k4_mcart_1 @ 
% 0.39/0.57                  (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X2 @ 
% 0.39/0.57                  X1 @ X0))
% 0.39/0.57          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.39/0.57          | ~ (r2_hidden @ X2 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((sk_A)
% 0.39/0.57            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.39/0.57          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.39/0.57               sk_C)
% 0.39/0.57          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_E_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['56', '61'])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.39/0.57        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('65', plain,
% 0.39/0.57      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_C)),
% 0.39/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((sk_A)
% 0.39/0.57            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.39/0.57          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_E_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['62', '65'])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_E_2)
% 0.39/0.57          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '66'])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.57          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.57  thf('72', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['68', '71'])).
% 0.39/0.57  thf('73', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_E_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['67', '72'])).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '73'])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.39/0.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.39/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.57          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.39/0.57  thf('79', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_2)),
% 0.39/0.57      inference('sup-', [status(thm)], ['75', '78'])).
% 0.39/0.57  thf('80', plain, (((sk_A) != (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['74', '79'])).
% 0.39/0.57  thf('81', plain, ($false), inference('simplify', [status(thm)], ['80'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
