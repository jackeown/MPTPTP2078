%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brrVXKv4op

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 200 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          : 1054 (2534 expanded)
%              Number of equality atoms :   40 ( 116 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

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
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( X6
        = ( k4_tarski @ ( sk_E @ X6 @ X5 @ X4 ) @ ( sk_F @ X6 @ X5 @ X4 ) ) )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k4_tarski @ ( sk_E @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) @ ( sk_F @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ ( sk_F @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_E @ X6 @ X5 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3
        = ( k4_tarski @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) )
    = ( k4_tarski @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( sk_F @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( sk_F @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X0 )
      = ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = ( k4_tarski @ ( sk_E @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ ( sk_F @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_mcart_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k3_mcart_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X1 @ X0 )
      = ( k4_mcart_1 @ ( sk_E @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ ( sk_F @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('36',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_B )
      | ~ ( r2_hidden @ X22 @ sk_C )
      | ~ ( r2_hidden @ X23 @ sk_D )
      | ( sk_A
       != ( k4_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ( sk_A
       != ( k4_mcart_1 @ ( sk_E @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_F @ X6 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_F @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( sk_E @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 )
      | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_F @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['7','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ) @ sk_E_1 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brrVXKv4op
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:42:49 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 95 iterations in 0.071s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.56  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.23/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.23/0.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.23/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.23/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.56  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.56  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.23/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.56  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.23/0.56  thf(t83_mcart_1, conjecture,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.56     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.23/0.56          ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.56            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.23/0.56                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.23/0.56                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.56        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.23/0.56             ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.56               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.23/0.56                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.23/0.56                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 0.23/0.56  thf('0', plain,
% 0.23/0.56      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(d4_zfmisc_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.23/0.56       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.56         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.23/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.56  thf(d10_xboole_0, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.56  thf('2', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.56  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.56  thf(t103_zfmisc_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.23/0.56          ( r2_hidden @ D @ A ) & 
% 0.23/0.56          ( ![E:$i,F:$i]:
% 0.23/0.56            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.23/0.56                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.23/0.56  thf('4', plain,
% 0.23/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.23/0.56          | ((X6) = (k4_tarski @ (sk_E @ X6 @ X5 @ X4) @ (sk_F @ X6 @ X5 @ X4)))
% 0.23/0.56          | ~ (r2_hidden @ X6 @ X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.56  thf('6', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.56          | ((X4)
% 0.23/0.56              = (k4_tarski @ (sk_E @ X4 @ X0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)) @ 
% 0.23/0.56                 (sk_F @ X4 @ X0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['1', '5'])).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (((sk_A)
% 0.23/0.56         = (k4_tarski @ 
% 0.23/0.56            (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56            (sk_F @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['0', '6'])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.56         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.23/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.56  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.56  thf('11', plain,
% 0.23/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X6 @ X5 @ X4) @ X4)
% 0.23/0.56          | ~ (r2_hidden @ X6 @ X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.23/0.56  thf('12', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.56  thf('13', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X4 @ X0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)) @ 
% 0.23/0.56             (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['9', '12'])).
% 0.23/0.56  thf('14', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56        (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.23/0.56      inference('sup-', [status(thm)], ['8', '13'])).
% 0.23/0.56  thf(d3_zfmisc_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.23/0.56       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.23/0.56  thf('15', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.56         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.23/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.56  thf('16', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.56          | ((X3)
% 0.23/0.56              = (k4_tarski @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.23/0.56                 (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (((sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))
% 0.23/0.56         = (k4_tarski @ 
% 0.23/0.56            (sk_E @ 
% 0.23/0.56             (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56             sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56            (sk_F @ 
% 0.23/0.56             (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56             sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.23/0.56  thf(d3_mcart_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.23/0.56  thf('19', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 0.23/0.56           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.56  thf('20', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ 
% 0.23/0.56           (sk_E @ 
% 0.23/0.56            (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56            sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56           (sk_F @ 
% 0.23/0.56            (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56            sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56           X0)
% 0.23/0.56           = (k4_tarski @ 
% 0.23/0.56              (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ X0))),
% 0.23/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.23/0.56  thf('21', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56        (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.23/0.56      inference('sup-', [status(thm)], ['8', '13'])).
% 0.23/0.56  thf('22', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.56         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.23/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.56  thf('23', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.56  thf('24', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.23/0.56             (k2_zfmisc_1 @ X2 @ X1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.56  thf('25', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56         sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.56      inference('sup-', [status(thm)], ['21', '24'])).
% 0.23/0.56  thf('26', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.56  thf('27', plain,
% 0.23/0.56      (((sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56         sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.23/0.56         = (k4_tarski @ 
% 0.23/0.56            (sk_E @ 
% 0.23/0.56             (sk_E @ 
% 0.23/0.56              (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56              sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56             sk_C @ sk_B) @ 
% 0.23/0.56            (sk_F @ 
% 0.23/0.56             (sk_E @ 
% 0.23/0.56              (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56              sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56             sk_C @ sk_B)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.56  thf('28', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 0.23/0.56           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.56  thf('29', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 0.23/0.56           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.23/0.56  thf('30', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.23/0.56           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.23/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.23/0.56  thf(d4_mcart_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.23/0.56       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.56  thf('31', plain,
% 0.23/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.56         ((k4_mcart_1 @ X13 @ X14 @ X15 @ X16)
% 0.23/0.56           = (k4_tarski @ (k3_mcart_1 @ X13 @ X14 @ X15) @ X16))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.23/0.56  thf('32', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.23/0.56           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.23/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.56  thf('33', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]:
% 0.23/0.56         ((k3_mcart_1 @ 
% 0.23/0.56           (sk_E @ 
% 0.23/0.56            (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56            sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56           X1 @ X0)
% 0.23/0.56           = (k4_mcart_1 @ 
% 0.23/0.56              (sk_E @ 
% 0.23/0.56               (sk_E @ 
% 0.23/0.56                (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56               sk_C @ sk_B) @ 
% 0.23/0.56              (sk_F @ 
% 0.23/0.56               (sk_E @ 
% 0.23/0.56                (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56               sk_C @ sk_B) @ 
% 0.23/0.56              X1 @ X0))),
% 0.23/0.56      inference('sup+', [status(thm)], ['27', '32'])).
% 0.23/0.56  thf('34', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56         sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.56      inference('sup-', [status(thm)], ['21', '24'])).
% 0.23/0.56  thf('35', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.56  thf('36', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ 
% 0.23/0.56         (sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56          sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56         sk_C @ sk_B) @ 
% 0.23/0.56        sk_B)),
% 0.23/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.56  thf('37', plain,
% 0.23/0.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X21 @ sk_B)
% 0.23/0.56          | ~ (r2_hidden @ X22 @ sk_C)
% 0.23/0.56          | ~ (r2_hidden @ X23 @ sk_D)
% 0.23/0.56          | ((sk_A) != (k4_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.23/0.56          | ~ (r2_hidden @ X24 @ sk_E_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('38', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X0 @ sk_E_1)
% 0.23/0.56          | ((sk_A)
% 0.23/0.56              != (k4_mcart_1 @ 
% 0.23/0.56                  (sk_E @ 
% 0.23/0.56                   (sk_E @ 
% 0.23/0.56                    (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                    sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56                   sk_C @ sk_B) @ 
% 0.23/0.56                  X2 @ X1 @ X0))
% 0.23/0.56          | ~ (r2_hidden @ X1 @ sk_D)
% 0.23/0.56          | ~ (r2_hidden @ X2 @ sk_C))),
% 0.23/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.56  thf('39', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]:
% 0.23/0.56         (((sk_A)
% 0.23/0.56            != (k3_mcart_1 @ 
% 0.23/0.56                (sk_E @ 
% 0.23/0.56                 (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                 sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56                X1 @ X0))
% 0.23/0.56          | ~ (r2_hidden @ 
% 0.23/0.56               (sk_F @ 
% 0.23/0.56                (sk_E @ 
% 0.23/0.56                 (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                 sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56                sk_C @ sk_B) @ 
% 0.23/0.56               sk_C)
% 0.23/0.56          | ~ (r2_hidden @ X1 @ sk_D)
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['33', '38'])).
% 0.23/0.56  thf('40', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56         sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.23/0.56      inference('sup-', [status(thm)], ['21', '24'])).
% 0.23/0.56  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.56  thf('42', plain,
% 0.23/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X4 @ X5))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X6 @ X5 @ X4) @ X5)
% 0.23/0.56          | ~ (r2_hidden @ X6 @ X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.23/0.56  thf('43', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.56  thf('44', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_F @ 
% 0.23/0.56         (sk_E @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56          sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56         sk_C @ sk_B) @ 
% 0.23/0.56        sk_C)),
% 0.23/0.56      inference('sup-', [status(thm)], ['40', '43'])).
% 0.23/0.56  thf('45', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]:
% 0.23/0.56         (((sk_A)
% 0.23/0.56            != (k3_mcart_1 @ 
% 0.23/0.56                (sk_E @ 
% 0.23/0.56                 (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                 sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56                X1 @ X0))
% 0.23/0.56          | ~ (r2_hidden @ X1 @ sk_D)
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['39', '44'])).
% 0.23/0.56  thf('46', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((sk_A)
% 0.23/0.56            != (k4_tarski @ 
% 0.23/0.56                (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                X0))
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_E_1)
% 0.23/0.56          | ~ (r2_hidden @ 
% 0.23/0.56               (sk_F @ 
% 0.23/0.56                (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56               sk_D))),
% 0.23/0.56      inference('sup-', [status(thm)], ['20', '45'])).
% 0.23/0.56  thf('47', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56        (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.23/0.56      inference('sup-', [status(thm)], ['8', '13'])).
% 0.23/0.56  thf('48', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.56         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.23/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.56  thf('49', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.56  thf('50', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.23/0.56  thf('51', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_F @ (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56         sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.23/0.56        sk_D)),
% 0.23/0.56      inference('sup-', [status(thm)], ['47', '50'])).
% 0.23/0.56  thf('52', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((sk_A)
% 0.23/0.56            != (k4_tarski @ 
% 0.23/0.56                (sk_E @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56                X0))
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_E_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['46', '51'])).
% 0.23/0.56  thf('53', plain,
% 0.23/0.56      ((((sk_A) != (sk_A))
% 0.23/0.56        | ~ (r2_hidden @ 
% 0.23/0.56             (sk_F @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ 
% 0.23/0.56             sk_E_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['7', '52'])).
% 0.23/0.56  thf('54', plain,
% 0.23/0.56      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('55', plain,
% 0.23/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.56         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.23/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.56  thf('56', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.56  thf('57', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ (sk_F @ X4 @ X0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf('58', plain,
% 0.23/0.56      ((r2_hidden @ 
% 0.23/0.56        (sk_F @ sk_A @ sk_E_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D)) @ sk_E_1)),
% 0.23/0.56      inference('sup-', [status(thm)], ['54', '57'])).
% 0.23/0.56  thf('59', plain, (((sk_A) != (sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['53', '58'])).
% 0.23/0.56  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.23/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
