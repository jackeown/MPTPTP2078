%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8UuEMCPTL

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 147 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  794 (1773 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t73_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
    <=> ( ( r2_hidden @ A @ D )
        & ( r2_hidden @ B @ E )
        & ( r2_hidden @ C @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
      <=> ( ( r2_hidden @ A @ D )
          & ( r2_hidden @ B @ E )
          & ( r2_hidden @ C @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_mcart_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) @ sk_F )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F )
    | ~ ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F )
   <= ~ ( r2_hidden @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
    | ( r2_hidden @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
   <= ( r2_hidden @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
   <= ( r2_hidden @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['16'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k4_tarski @ X9 @ X10 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X11 ) @ X13 )
      | ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X10 @ X13 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_E ) ) )
   <= ( r2_hidden @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_C @ sk_F )
   <= ( r2_hidden @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X10 @ X13 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) )
   <= ( r2_hidden @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E )
      & ( r2_hidden @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( ( r2_hidden @ sk_A @ sk_D )
      & ( r2_hidden @ sk_B @ sk_E )
      & ( r2_hidden @ sk_C @ sk_F ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['12'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_C @ sk_F )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) ) @ sk_E )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_E )
   <= ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['12'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('51',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) ) @ sk_D )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D )
   <= ~ ( r2_hidden @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( r2_hidden @ sk_A @ sk_D )
    | ~ ( r2_hidden @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['12'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_D )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['16'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','33','48','55','56','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8UuEMCPTL
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 194 iterations in 0.168s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.41/0.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.61  thf(t73_mcart_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.61     ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 0.41/0.61       ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & ( r2_hidden @ C @ F ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.61        ( ( r2_hidden @
% 0.41/0.61            ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 0.41/0.61          ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & 
% 0.41/0.61            ( r2_hidden @ C @ F ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t73_mcart_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (((r2_hidden @ sk_C @ sk_F)
% 0.41/0.61        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.61           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (((r2_hidden @ sk_C @ sk_F)) | 
% 0.41/0.61       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.61         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_D)
% 0.41/0.61        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.61           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf(d3_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.41/0.62       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.41/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.41/0.62  thf(t10_mcart_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.41/0.62       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.41/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.62         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.41/0.62          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.41/0.62          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (((r2_hidden @ (k2_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) @ sk_F))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '6'])).
% 0.41/0.62  thf(d3_mcart_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.41/0.62           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.41/0.62  thf(t7_mcart_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.41/0.62       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (((r2_hidden @ sk_C @ sk_F))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('demod', [status(thm)], ['7', '10'])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      ((~ (r2_hidden @ sk_C @ sk_F)
% 0.41/0.62        | ~ (r2_hidden @ sk_B @ sk_E)
% 0.41/0.62        | ~ (r2_hidden @ sk_A @ sk_D)
% 0.41/0.62        | ~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      ((~ (r2_hidden @ sk_C @ sk_F)) <= (~ ((r2_hidden @ sk_C @ sk_F)))),
% 0.41/0.62      inference('split', [status(esa)], ['12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (~
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))) | 
% 0.41/0.62       ((r2_hidden @ sk_C @ sk_F))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (((r2_hidden @ sk_A @ sk_D)) <= (((r2_hidden @ sk_A @ sk_D)))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (((r2_hidden @ sk_B @ sk_E)
% 0.41/0.62        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (((r2_hidden @ sk_B @ sk_E)) <= (((r2_hidden @ sk_B @ sk_E)))),
% 0.41/0.62      inference('split', [status(esa)], ['16'])).
% 0.41/0.62  thf(t11_mcart_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.41/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.41/0.62       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.41/0.62         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (((X11) != (k4_tarski @ X9 @ X10))
% 0.41/0.62          | ~ (r2_hidden @ (k1_mcart_1 @ X11) @ X12)
% 0.41/0.62          | ~ (r2_hidden @ (k2_mcart_1 @ X11) @ X13)
% 0.41/0.62          | (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.41/0.62          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X13)
% 0.41/0.62          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X12))),
% 0.41/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.41/0.62          | ~ (r2_hidden @ X10 @ X13)
% 0.41/0.62          | ~ (r2_hidden @ X9 @ X12))),
% 0.41/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((![X0 : $i, X1 : $i]:
% 0.41/0.62          (~ (r2_hidden @ X1 @ X0)
% 0.41/0.62           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_E))))
% 0.41/0.62         <= (((r2_hidden @ sk_B @ sk_E)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.41/0.62         <= (((r2_hidden @ sk_A @ sk_D)) & ((r2_hidden @ sk_B @ sk_E)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['15', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (((r2_hidden @ sk_C @ sk_F)) <= (((r2_hidden @ sk_C @ sk_F)))),
% 0.41/0.62      inference('split', [status(esa)], ['0'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.41/0.62          | ~ (r2_hidden @ X10 @ X13)
% 0.41/0.62          | ~ (r2_hidden @ X9 @ X12))),
% 0.41/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      ((![X0 : $i, X1 : $i]:
% 0.41/0.62          (~ (r2_hidden @ X1 @ X0)
% 0.41/0.62           | (r2_hidden @ (k4_tarski @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_F))))
% 0.41/0.62         <= (((r2_hidden @ sk_C @ sk_F)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (((r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 0.41/0.62         (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_E) @ sk_F)))
% 0.41/0.62         <= (((r2_hidden @ sk_A @ sk_D)) & 
% 0.41/0.62             ((r2_hidden @ sk_B @ sk_E)) & 
% 0.41/0.62             ((r2_hidden @ sk_C @ sk_F)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['24', '27'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.41/0.62           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.41/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.41/0.62         <= (((r2_hidden @ sk_A @ sk_D)) & 
% 0.41/0.62             ((r2_hidden @ sk_B @ sk_E)) & 
% 0.41/0.62             ((r2_hidden @ sk_C @ sk_F)))),
% 0.41/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62           (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.41/0.62         <= (~
% 0.41/0.62             ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('split', [status(esa)], ['12'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (~ ((r2_hidden @ sk_A @ sk_D)) | ~ ((r2_hidden @ sk_B @ sk_E)) | 
% 0.41/0.62       ~ ((r2_hidden @ sk_C @ sk_F)) | 
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.41/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.62         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.41/0.62          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.41/0.62          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (((r2_hidden @ (k1_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.41/0.62         (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.41/0.62           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('demod', [status(thm)], ['38', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.62         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.41/0.62          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (((r2_hidden @ (k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) @ sk_E))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (((r2_hidden @ sk_B @ sk_E))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      ((~ (r2_hidden @ sk_B @ sk_E)) <= (~ ((r2_hidden @ sk_B @ sk_E)))),
% 0.41/0.62      inference('split', [status(esa)], ['12'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (((r2_hidden @ sk_B @ sk_E)) | 
% 0.41/0.62       ~
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E)))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('demod', [status(thm)], ['38', '41'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.62         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.41/0.62          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (((r2_hidden @ (k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) @ sk_D))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (((r2_hidden @ sk_A @ sk_D))
% 0.41/0.62         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62               (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      ((~ (r2_hidden @ sk_A @ sk_D)) <= (~ ((r2_hidden @ sk_A @ sk_D)))),
% 0.41/0.62      inference('split', [status(esa)], ['12'])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (((r2_hidden @ sk_A @ sk_D)) | 
% 0.41/0.62       ~
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (~
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))) | 
% 0.41/0.62       ~ ((r2_hidden @ sk_A @ sk_D)) | ~ ((r2_hidden @ sk_B @ sk_E)) | 
% 0.41/0.62       ~ ((r2_hidden @ sk_C @ sk_F))),
% 0.41/0.62      inference('split', [status(esa)], ['12'])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (((r2_hidden @ sk_A @ sk_D)) | 
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (((r2_hidden @ sk_B @ sk_E)) | 
% 0.41/0.62       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62         (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.62      inference('split', [status(esa)], ['16'])).
% 0.41/0.62  thf('59', plain, ($false),
% 0.41/0.62      inference('sat_resolution*', [status(thm)],
% 0.41/0.62                ['1', '14', '33', '48', '55', '56', '57', '58'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
