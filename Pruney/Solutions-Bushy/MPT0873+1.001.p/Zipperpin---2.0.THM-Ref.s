%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yIdqobgmjh

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 292 expanded)
%              Number of leaves         :   19 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  554 (3262 expanded)
%              Number of equality atoms :   96 ( 549 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf('#_fresh_sk6_type',type,(
    '#_fresh_sk6': $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf('#_fresh_sk4_type',type,(
    '#_fresh_sk4': $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t33_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_mcart_1 @ A @ B @ C @ D )
          = ( k4_mcart_1 @ E @ F @ G @ H ) )
       => ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_mcart_1])).

thf('0',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 = X10 )
      | ( ( k4_tarski @ X11 @ X13 )
       != ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X11 @ X13 ) )
      = X11 ) ),
    inference(inj_rec,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('7',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X5 = X4 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ( sk_E = X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_E = sk_A ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_A @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('13',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_A @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X6 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('15',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk4' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X8 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('16',plain,
    ( ( '#_fresh_sk4' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_F ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk4' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X8 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('18',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_A @ sk_B @ sk_G ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X9 = X7 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('21',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk6' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X9 ) ),
    inference(inj_rec,[status(thm)],['20'])).

thf('22',plain,
    ( ( '#_fresh_sk6' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_G ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk6' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X9 ) ),
    inference(inj_rec,[status(thm)],['20'])).

thf('24',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['16','17'])).

thf('28',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_E = sk_A ),
    inference(eq_res,[status(thm)],['10'])).

thf('32',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['25'])).

thf('33',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_E = sk_A ),
    inference(eq_res,[status(thm)],['10'])).

thf('37',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ X0 )
      = ( k4_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ X0 )
      = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_E = sk_A ),
    inference(eq_res,[status(thm)],['10'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ X0 )
      = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_H ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( ( k4_tarski @ X11 @ X13 )
       != ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('48',plain,(
    ! [X11: $i,X13: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ X11 @ X13 ) )
      = X13 ) ),
    inference(inj_rec,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = sk_H ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('52',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['25'])).

thf('54',plain,
    ( ( sk_D != sk_D )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_C != sk_G )
    | ( sk_D != sk_H )
    | ( sk_A != sk_E )
    | ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('57',plain,(
    sk_C != sk_G ),
    inference('sat_resolution*',[status(thm)],['30','34','55','56'])).

thf('58',plain,(
    sk_C != sk_G ),
    inference(simpl_trail,[status(thm)],['26','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','58'])).


%------------------------------------------------------------------------------
