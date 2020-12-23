%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oVHS8w3Gbx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:17 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 303 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  877 (3502 expanded)
%              Number of equality atoms :   63 ( 197 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
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
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
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
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('38',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('44',plain,(
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('45',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) )
    = ( sk_E @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_mcart_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k3_mcart_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 )
      = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('55',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( r2_hidden @ X24 @ sk_C )
      | ~ ( r2_hidden @ X25 @ sk_D_1 )
      | ( sk_A
       != ( k4_mcart_1 @ X23 @ X24 @ X25 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ( sk_A
       != ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('61',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','62'])).

thf('64',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['12','69'])).

thf('71',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E_1 ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oVHS8w3Gbx
% 0.17/0.37  % Computer   : n011.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 14:49:27 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 81 iterations in 0.046s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.23/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.53  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.23/0.53  thf(sk_D_type, type, sk_D: $i > $i).
% 0.23/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.23/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.23/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.53  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(sk_E_type, type, sk_E: $i > $i).
% 0.23/0.53  thf(t83_mcart_1, conjecture,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.53     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.23/0.53          ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.53            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.23/0.53                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.23/0.53                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.53        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.23/0.53             ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.53               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.23/0.53                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.23/0.53                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(d4_zfmisc_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.23/0.53       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.53         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.23/0.53           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.53  thf(l139_zfmisc_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.23/0.53          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.23/0.53      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.53          | ((k4_tarski @ (sk_D @ X4) @ (sk_E @ X4)) = (X4)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.53  thf('5', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.53  thf(t7_mcart_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.23/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.23/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.53  thf('9', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('11', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.23/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.53  thf('12', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.53         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.23/0.53           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.53  thf(t10_mcart_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.23/0.53       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.23/0.53         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.23/0.53  thf('15', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.53          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.53  thf(d3_zfmisc_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.23/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.53         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.23/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.23/0.53      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.23/0.53  thf('20', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.53          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_D @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('25', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['21', '24'])).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['21', '24'])).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_A)) = (sk_E @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53         (k2_mcart_1 @ (k1_mcart_1 @ sk_A))) = (k1_mcart_1 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['25', '28'])).
% 0.23/0.53  thf(d3_mcart_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.23/0.53           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.53  thf('31', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.23/0.53           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.53  thf('33', plain,
% 0.23/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.53         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.23/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.53  thf('34', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.53          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.23/0.53      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.23/0.53  thf('38', plain,
% 0.23/0.53      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.23/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.53  thf('39', plain,
% 0.23/0.53      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.23/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.53  thf('40', plain,
% 0.23/0.53      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('41', plain,
% 0.23/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.23/0.53         = (sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.23/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['38', '41'])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53         (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.23/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['38', '41'])).
% 0.23/0.53  thf('44', plain,
% 0.23/0.53      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))
% 0.23/0.53         = (sk_E @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53         (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))
% 0.23/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['42', '45'])).
% 0.23/0.53  thf('47', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.23/0.53           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.23/0.53           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.53  thf('49', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.23/0.53           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.23/0.53      inference('sup+', [status(thm)], ['47', '48'])).
% 0.23/0.53  thf(d4_mcart_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.23/0.53       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.53  thf('50', plain,
% 0.23/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.53         ((k4_mcart_1 @ X9 @ X10 @ X11 @ X12)
% 0.23/0.53           = (k4_tarski @ (k3_mcart_1 @ X9 @ X10 @ X11) @ X12))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.23/0.53  thf('51', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.23/0.53           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.23/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.53  thf('52', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0)
% 0.23/0.53           = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53              (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['46', '51'])).
% 0.23/0.53  thf('53', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.53  thf('54', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('55', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_B)),
% 0.23/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.53  thf('56', plain,
% 0.23/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X23 @ sk_B)
% 0.23/0.53          | ~ (r2_hidden @ X24 @ sk_C)
% 0.23/0.53          | ~ (r2_hidden @ X25 @ sk_D_1)
% 0.23/0.53          | ((sk_A) != (k4_mcart_1 @ X23 @ X24 @ X25 @ X26))
% 0.23/0.53          | ~ (r2_hidden @ X26 @ sk_E_1))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('57', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X0 @ sk_E_1)
% 0.23/0.53          | ((sk_A)
% 0.23/0.53              != (k4_mcart_1 @ 
% 0.23/0.53                  (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X2 @ 
% 0.23/0.53                  X1 @ X0))
% 0.23/0.53          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.23/0.53          | ~ (r2_hidden @ X2 @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.53  thf('58', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((sk_A)
% 0.23/0.53            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.23/0.53          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.23/0.53               sk_C)
% 0.23/0.53          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.23/0.53          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['52', '57'])).
% 0.23/0.53  thf('59', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.23/0.53        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.53  thf('60', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('61', plain,
% 0.23/0.53      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_C)),
% 0.23/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.23/0.53  thf('62', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((sk_A)
% 0.23/0.53            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.23/0.53          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.23/0.53          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.53      inference('demod', [status(thm)], ['58', '61'])).
% 0.23/0.53  thf('63', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ sk_E_1)
% 0.23/0.53          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['31', '62'])).
% 0.23/0.53  thf('64', plain,
% 0.23/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.53  thf('65', plain,
% 0.23/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.53         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.23/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.53  thf('66', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('67', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.53          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.53  thf('68', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D_1)),
% 0.23/0.53      inference('sup-', [status(thm)], ['64', '67'])).
% 0.23/0.53  thf('69', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.53      inference('demod', [status(thm)], ['63', '68'])).
% 0.23/0.53  thf('70', plain,
% 0.23/0.53      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['12', '69'])).
% 0.23/0.53  thf('71', plain,
% 0.23/0.53      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('72', plain,
% 0.23/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.53         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.23/0.53           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.53  thf('73', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.53         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.23/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.53  thf('74', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.53          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.23/0.53  thf('75', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E_1)),
% 0.23/0.53      inference('sup-', [status(thm)], ['71', '74'])).
% 0.23/0.53  thf('76', plain, (((sk_A) != (sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['70', '75'])).
% 0.23/0.53  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
