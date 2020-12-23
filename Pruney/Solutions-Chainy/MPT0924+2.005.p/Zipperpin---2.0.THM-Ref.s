%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EwXKzsc2Zo

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:18 EST 2020

% Result     : Theorem 25.73s
% Output     : Refutation 25.73s
% Verified   : 
% Statistics : Number of formulae       :  130 (1245 expanded)
%              Number of leaves         :   26 ( 383 expanded)
%              Depth                    :   22
%              Number of atoms          : 1504 (17421 expanded)
%              Number of equality atoms :   32 ( 675 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(t84_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( r2_hidden @ ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
    <=> ( ( r2_hidden @ A @ E )
        & ( r2_hidden @ B @ F )
        & ( r2_hidden @ C @ G )
        & ( r2_hidden @ D @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( r2_hidden @ ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
      <=> ( ( r2_hidden @ A @ E )
          & ( r2_hidden @ B @ F )
          & ( r2_hidden @ C @ G )
          & ( r2_hidden @ D @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k3_mcart_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t73_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
    <=> ( ( r2_hidden @ A @ D )
        & ( r2_hidden @ B @ E )
        & ( r2_hidden @ C @ F ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X30 @ X32 @ X33 ) @ ( k3_zfmisc_1 @ X31 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X6 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ X34 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X30 @ X32 @ X33 ) @ ( k3_zfmisc_1 @ X31 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ X1 @ X5 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X5 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X1 @ ( k4_tarski @ X1 @ sk_C ) @ sk_G @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('32',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ X34 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X30 @ X32 @ X33 ) @ ( k3_zfmisc_1 @ X31 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_F_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_F_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X30 @ X32 @ X33 ) @ ( k3_zfmisc_1 @ X31 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E_2 )
   <= ~ ( r2_hidden @ sk_A @ sk_E_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('50',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X33 @ X35 )
      | ~ ( r2_hidden @ ( k3_mcart_1 @ X30 @ X32 @ X33 ) @ ( k3_zfmisc_1 @ X31 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t73_mcart_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( r2_hidden @ X0 @ X4 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_mcart_1 @ X7 @ X6 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_H )
   <= ~ ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_G )
   <= ~ ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
    | ~ ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ sk_C @ sk_G )
    | ~ ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sat_resolution*',[status(thm)],['41','46','55','58','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(simpl_trail,[status(thm)],['1','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
   <= ( r2_hidden @ sk_A @ sk_E_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
   <= ( r2_hidden @ sk_B @ sk_F_2 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('66',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X1 @ ( k4_tarski @ X1 @ sk_B ) @ sk_F_2 @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( zip_tseitin_0 @ sk_B @ sk_A @ ( k4_tarski @ sk_A @ sk_B ) @ sk_F_2 @ sk_E_2 )
   <= ( ( r2_hidden @ sk_A @ sk_E_2 )
      & ( r2_hidden @ sk_B @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('69',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_E_2 )
      & ( r2_hidden @ sk_B @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
   <= ( r2_hidden @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X1 @ ( k4_tarski @ X1 @ sk_C ) @ sk_G @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_E_2 )
      & ( r2_hidden @ sk_B @ sk_F_2 )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('76',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_E_2 )
      & ( r2_hidden @ sk_B @ sk_F_2 )
      & ( r2_hidden @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,(
    r2_hidden @ sk_A @ sk_E_2 ),
    inference('sat_resolution*',[status(thm)],['41','46','55','58','59','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['63'])).

thf('80',plain,(
    r2_hidden @ sk_B @ sk_F_2 ),
    inference('sat_resolution*',[status(thm)],['41','46','55','58','59','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_C @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['70'])).

thf('82',plain,(
    r2_hidden @ sk_C @ sk_G ),
    inference('sat_resolution*',[status(thm)],['41','46','55','58','59','81'])).

thf('83',plain,(
    zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(simpl_trail,[status(thm)],['76','78','80','82'])).

thf('84',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('85',plain,(
    r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('87',plain,(
    r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
   <= ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ ( k4_tarski @ X1 @ sk_D_1 ) @ sk_H @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['88'])).

thf('93',plain,(
    r2_hidden @ sk_D_1 @ sk_H ),
    inference('sat_resolution*',[status(thm)],['41','46','55','58','59','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ ( k4_tarski @ X1 @ sk_D_1 ) @ sk_H @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    zip_tseitin_0 @ sk_D_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k4_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ sk_H @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k3_mcart_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('97',plain,(
    zip_tseitin_0 @ sk_D_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ sk_H @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('99',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) @ sk_H ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('101',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['61','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EwXKzsc2Zo
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 25.73/25.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.73/25.92  % Solved by: fo/fo7.sh
% 25.73/25.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.73/25.92  % done 3807 iterations in 25.458s
% 25.73/25.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.73/25.92  % SZS output start Refutation
% 25.73/25.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 25.73/25.92  thf(sk_A_type, type, sk_A: $i).
% 25.73/25.92  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 25.73/25.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 25.73/25.92  thf(sk_B_type, type, sk_B: $i).
% 25.73/25.92  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 25.73/25.92  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 25.73/25.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 25.73/25.92  thf(sk_D_1_type, type, sk_D_1: $i).
% 25.73/25.92  thf(sk_H_type, type, sk_H: $i).
% 25.73/25.92  thf(sk_C_type, type, sk_C: $i).
% 25.73/25.92  thf(sk_G_type, type, sk_G: $i).
% 25.73/25.92  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 25.73/25.92  thf(sk_E_2_type, type, sk_E_2: $i).
% 25.73/25.92  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 25.73/25.92  thf(sk_F_2_type, type, sk_F_2: $i).
% 25.73/25.92  thf(t84_mcart_1, conjecture,
% 25.73/25.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 25.73/25.92     ( ( r2_hidden @
% 25.73/25.92         ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 25.73/25.92       ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 25.73/25.92         ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ))).
% 25.73/25.92  thf(zf_stmt_0, negated_conjecture,
% 25.73/25.92    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 25.73/25.92        ( ( r2_hidden @
% 25.73/25.92            ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 25.73/25.92          ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 25.73/25.92            ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ) )),
% 25.73/25.92    inference('cnf.neg', [status(esa)], [t84_mcart_1])).
% 25.73/25.92  thf('0', plain,
% 25.73/25.92      ((~ (r2_hidden @ sk_D_1 @ sk_H)
% 25.73/25.92        | ~ (r2_hidden @ sk_C @ sk_G)
% 25.73/25.92        | ~ (r2_hidden @ sk_B @ sk_F_2)
% 25.73/25.92        | ~ (r2_hidden @ sk_A @ sk_E_2)
% 25.73/25.92        | ~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92             (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.73/25.92  thf('1', plain,
% 25.73/25.92      ((~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 25.73/25.92         <= (~
% 25.73/25.92             ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('2', plain,
% 25.73/25.92      (((r2_hidden @ sk_A @ sk_E_2)
% 25.73/25.92        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.73/25.92  thf('3', plain,
% 25.73/25.92      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('split', [status(esa)], ['2'])).
% 25.73/25.92  thf(d3_zfmisc_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i]:
% 25.73/25.92     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 25.73/25.92       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 25.73/25.92  thf('4', plain,
% 25.73/25.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 25.73/25.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.73/25.92  thf('5', plain,
% 25.73/25.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 25.73/25.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.73/25.92  thf('6', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 25.73/25.92      inference('sup+', [status(thm)], ['4', '5'])).
% 25.73/25.92  thf(d4_zfmisc_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i,D:$i]:
% 25.73/25.92     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 25.73/25.92       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 25.73/25.92  thf('7', plain,
% 25.73/25.92      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.73/25.92         ((k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25)
% 25.73/25.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X22 @ X23 @ X24) @ X25))),
% 25.73/25.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 25.73/25.92  thf('8', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['6', '7'])).
% 25.73/25.92  thf(d3_mcart_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i]:
% 25.73/25.92     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 25.73/25.92  thf('9', plain,
% 25.73/25.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.73/25.92  thf('10', plain,
% 25.73/25.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.73/25.92  thf('11', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 25.73/25.92      inference('sup+', [status(thm)], ['9', '10'])).
% 25.73/25.92  thf(t31_mcart_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i,D:$i]:
% 25.73/25.92     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 25.73/25.92       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 25.73/25.92  thf('12', plain,
% 25.73/25.92      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 25.73/25.92         ((k4_mcart_1 @ X26 @ X27 @ X28 @ X29)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28) @ X29))),
% 25.73/25.92      inference('cnf', [status(esa)], [t31_mcart_1])).
% 25.73/25.92  thf('13', plain,
% 25.73/25.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.73/25.92  thf('14', plain,
% 25.73/25.92      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 25.73/25.92         ((k4_mcart_1 @ X26 @ X27 @ X28 @ X29)
% 25.73/25.92           = (k4_tarski @ (k3_mcart_1 @ X26 @ X27 @ X28) @ X29))),
% 25.73/25.92      inference('demod', [status(thm)], ['12', '13'])).
% 25.73/25.92  thf('15', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['11', '14'])).
% 25.73/25.92  thf(t73_mcart_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 25.73/25.92     ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 25.73/25.92       ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & ( r2_hidden @ C @ F ) ) ))).
% 25.73/25.92  thf('16', plain,
% 25.73/25.92      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 25.73/25.92         ((r2_hidden @ X30 @ X31)
% 25.73/25.92          | ~ (r2_hidden @ (k3_mcart_1 @ X30 @ X32 @ X33) @ 
% 25.73/25.92               (k3_zfmisc_1 @ X31 @ X34 @ X35)))),
% 25.73/25.92      inference('cnf', [status(esa)], [t73_mcart_1])).
% 25.73/25.92  thf('17', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 25.73/25.92             (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 25.73/25.92          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ X6))),
% 25.73/25.92      inference('sup-', [status(thm)], ['15', '16'])).
% 25.73/25.92  thf('18', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 25.73/25.92             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 25.73/25.92          | (r2_hidden @ (k4_tarski @ X7 @ X6) @ (k2_zfmisc_1 @ X3 @ X2)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['8', '17'])).
% 25.73/25.92  thf('19', plain,
% 25.73/25.92      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['3', '18'])).
% 25.73/25.92  thf('20', plain,
% 25.73/25.92      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('split', [status(esa)], ['2'])).
% 25.73/25.92  thf('21', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['6', '7'])).
% 25.73/25.92  thf('22', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['11', '14'])).
% 25.73/25.92  thf('23', plain,
% 25.73/25.92      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 25.73/25.92         ((r2_hidden @ X32 @ X34)
% 25.73/25.92          | ~ (r2_hidden @ (k3_mcart_1 @ X30 @ X32 @ X33) @ 
% 25.73/25.92               (k3_zfmisc_1 @ X31 @ X34 @ X35)))),
% 25.73/25.92      inference('cnf', [status(esa)], [t73_mcart_1])).
% 25.73/25.92  thf('24', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 25.73/25.92             (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 25.73/25.92          | (r2_hidden @ X1 @ X5))),
% 25.73/25.92      inference('sup-', [status(thm)], ['22', '23'])).
% 25.73/25.92  thf('25', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 25.73/25.92             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 25.73/25.92          | (r2_hidden @ X5 @ X1))),
% 25.73/25.92      inference('sup-', [status(thm)], ['21', '24'])).
% 25.73/25.92  thf('26', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['20', '25'])).
% 25.73/25.92  thf(d2_zfmisc_1, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i]:
% 25.73/25.92     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 25.73/25.92       ( ![D:$i]:
% 25.73/25.92         ( ( r2_hidden @ D @ C ) <=>
% 25.73/25.92           ( ?[E:$i,F:$i]:
% 25.73/25.92             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 25.73/25.92               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 25.73/25.92  thf(zf_stmt_1, axiom,
% 25.73/25.92    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 25.73/25.92     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 25.73/25.92       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 25.73/25.92         ( r2_hidden @ E @ A ) ) ))).
% 25.73/25.92  thf('27', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 25.73/25.92         ((zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5)
% 25.73/25.92          | ~ (r2_hidden @ X0 @ X5)
% 25.73/25.92          | ~ (r2_hidden @ X1 @ X3)
% 25.73/25.92          | ((X2) != (k4_tarski @ X0 @ X1)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.73/25.92  thf('28', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 25.73/25.92         (~ (r2_hidden @ X1 @ X3)
% 25.73/25.92          | ~ (r2_hidden @ X0 @ X5)
% 25.73/25.92          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 25.73/25.92      inference('simplify', [status(thm)], ['27'])).
% 25.73/25.92  thf('29', plain,
% 25.73/25.92      ((![X0 : $i, X1 : $i]:
% 25.73/25.92          ((zip_tseitin_0 @ sk_C @ X1 @ (k4_tarski @ X1 @ sk_C) @ sk_G @ X0)
% 25.73/25.92           | ~ (r2_hidden @ X1 @ X0)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['26', '28'])).
% 25.73/25.92  thf('30', plain,
% 25.73/25.92      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ sk_G @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['19', '29'])).
% 25.73/25.92  thf('31', plain,
% 25.73/25.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.73/25.92  thf('32', plain,
% 25.73/25.92      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_G @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('demod', [status(thm)], ['30', '31'])).
% 25.73/25.92  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 25.73/25.92  thf(zf_stmt_3, axiom,
% 25.73/25.92    (![A:$i,B:$i,C:$i]:
% 25.73/25.92     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 25.73/25.92       ( ![D:$i]:
% 25.73/25.92         ( ( r2_hidden @ D @ C ) <=>
% 25.73/25.92           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 25.73/25.92  thf('33', plain,
% 25.73/25.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 25.73/25.92         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 25.73/25.92          | (r2_hidden @ X8 @ X11)
% 25.73/25.92          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 25.73/25.92  thf('34', plain,
% 25.73/25.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 25.73/25.92         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 25.73/25.92          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 25.73/25.92      inference('simplify', [status(thm)], ['33'])).
% 25.73/25.92  thf('35', plain,
% 25.73/25.92      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92         (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E_2 @ sk_F_2) @ sk_G)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['32', '34'])).
% 25.73/25.92  thf('36', plain,
% 25.73/25.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 25.73/25.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.73/25.92  thf('37', plain,
% 25.73/25.92      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92         (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('demod', [status(thm)], ['35', '36'])).
% 25.73/25.92  thf('38', plain,
% 25.73/25.92      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 25.73/25.92         ((r2_hidden @ X32 @ X34)
% 25.73/25.92          | ~ (r2_hidden @ (k3_mcart_1 @ X30 @ X32 @ X33) @ 
% 25.73/25.92               (k3_zfmisc_1 @ X31 @ X34 @ X35)))),
% 25.73/25.92      inference('cnf', [status(esa)], [t73_mcart_1])).
% 25.73/25.92  thf('39', plain,
% 25.73/25.92      (((r2_hidden @ sk_B @ sk_F_2))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['37', '38'])).
% 25.73/25.92  thf('40', plain,
% 25.73/25.92      ((~ (r2_hidden @ sk_B @ sk_F_2)) <= (~ ((r2_hidden @ sk_B @ sk_F_2)))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('41', plain,
% 25.73/25.92      (((r2_hidden @ sk_B @ sk_F_2)) | 
% 25.73/25.92       ~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['39', '40'])).
% 25.73/25.92  thf('42', plain,
% 25.73/25.92      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92         (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('demod', [status(thm)], ['35', '36'])).
% 25.73/25.92  thf('43', plain,
% 25.73/25.92      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 25.73/25.92         ((r2_hidden @ X30 @ X31)
% 25.73/25.92          | ~ (r2_hidden @ (k3_mcart_1 @ X30 @ X32 @ X33) @ 
% 25.73/25.92               (k3_zfmisc_1 @ X31 @ X34 @ X35)))),
% 25.73/25.92      inference('cnf', [status(esa)], [t73_mcart_1])).
% 25.73/25.92  thf('44', plain,
% 25.73/25.92      (((r2_hidden @ sk_A @ sk_E_2))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['42', '43'])).
% 25.73/25.92  thf('45', plain,
% 25.73/25.92      ((~ (r2_hidden @ sk_A @ sk_E_2)) <= (~ ((r2_hidden @ sk_A @ sk_E_2)))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('46', plain,
% 25.73/25.92      (((r2_hidden @ sk_A @ sk_E_2)) | 
% 25.73/25.92       ~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['44', '45'])).
% 25.73/25.92  thf('47', plain,
% 25.73/25.92      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('split', [status(esa)], ['2'])).
% 25.73/25.92  thf('48', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['6', '7'])).
% 25.73/25.92  thf('49', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 25.73/25.92           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 25.73/25.92      inference('demod', [status(thm)], ['11', '14'])).
% 25.73/25.92  thf('50', plain,
% 25.73/25.92      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 25.73/25.92         ((r2_hidden @ X33 @ X35)
% 25.73/25.92          | ~ (r2_hidden @ (k3_mcart_1 @ X30 @ X32 @ X33) @ 
% 25.73/25.92               (k3_zfmisc_1 @ X31 @ X34 @ X35)))),
% 25.73/25.92      inference('cnf', [status(esa)], [t73_mcart_1])).
% 25.73/25.92  thf('51', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ 
% 25.73/25.92             (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 25.73/25.92          | (r2_hidden @ X0 @ X4))),
% 25.73/25.92      inference('sup-', [status(thm)], ['49', '50'])).
% 25.73/25.92  thf('52', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 25.73/25.92         (~ (r2_hidden @ (k4_mcart_1 @ X7 @ X6 @ X5 @ X4) @ 
% 25.73/25.92             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 25.73/25.92          | (r2_hidden @ X4 @ X0))),
% 25.73/25.92      inference('sup-', [status(thm)], ['48', '51'])).
% 25.73/25.92  thf('53', plain,
% 25.73/25.92      (((r2_hidden @ sk_D_1 @ sk_H))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['47', '52'])).
% 25.73/25.92  thf('54', plain,
% 25.73/25.92      ((~ (r2_hidden @ sk_D_1 @ sk_H)) <= (~ ((r2_hidden @ sk_D_1 @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('55', plain,
% 25.73/25.92      (((r2_hidden @ sk_D_1 @ sk_H)) | 
% 25.73/25.92       ~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['53', '54'])).
% 25.73/25.92  thf('56', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G))
% 25.73/25.92         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 25.73/25.92      inference('sup-', [status(thm)], ['20', '25'])).
% 25.73/25.92  thf('57', plain,
% 25.73/25.92      ((~ (r2_hidden @ sk_C @ sk_G)) <= (~ ((r2_hidden @ sk_C @ sk_G)))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('58', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G)) | 
% 25.73/25.92       ~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['56', '57'])).
% 25.73/25.92  thf('59', plain,
% 25.73/25.92      (~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))) | 
% 25.73/25.92       ~ ((r2_hidden @ sk_B @ sk_F_2)) | ~ ((r2_hidden @ sk_A @ sk_E_2)) | 
% 25.73/25.92       ~ ((r2_hidden @ sk_C @ sk_G)) | ~ ((r2_hidden @ sk_D_1 @ sk_H))),
% 25.73/25.92      inference('split', [status(esa)], ['0'])).
% 25.73/25.92  thf('60', plain,
% 25.73/25.92      (~
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('sat_resolution*', [status(thm)],
% 25.73/25.92                ['41', '46', '55', '58', '59'])).
% 25.73/25.92  thf('61', plain,
% 25.73/25.92      (~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92          (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))),
% 25.73/25.92      inference('simpl_trail', [status(thm)], ['1', '60'])).
% 25.73/25.92  thf('62', plain,
% 25.73/25.92      (((r2_hidden @ sk_A @ sk_E_2)) <= (((r2_hidden @ sk_A @ sk_E_2)))),
% 25.73/25.92      inference('split', [status(esa)], ['2'])).
% 25.73/25.92  thf('63', plain,
% 25.73/25.92      (((r2_hidden @ sk_B @ sk_F_2)
% 25.73/25.92        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.73/25.92  thf('64', plain,
% 25.73/25.92      (((r2_hidden @ sk_B @ sk_F_2)) <= (((r2_hidden @ sk_B @ sk_F_2)))),
% 25.73/25.92      inference('split', [status(esa)], ['63'])).
% 25.73/25.92  thf('65', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 25.73/25.92         (~ (r2_hidden @ X1 @ X3)
% 25.73/25.92          | ~ (r2_hidden @ X0 @ X5)
% 25.73/25.92          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 25.73/25.92      inference('simplify', [status(thm)], ['27'])).
% 25.73/25.92  thf('66', plain,
% 25.73/25.92      ((![X0 : $i, X1 : $i]:
% 25.73/25.92          ((zip_tseitin_0 @ sk_B @ X1 @ (k4_tarski @ X1 @ sk_B) @ sk_F_2 @ X0)
% 25.73/25.92           | ~ (r2_hidden @ X1 @ X0)))
% 25.73/25.92         <= (((r2_hidden @ sk_B @ sk_F_2)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['64', '65'])).
% 25.73/25.92  thf('67', plain,
% 25.73/25.92      (((zip_tseitin_0 @ sk_B @ sk_A @ (k4_tarski @ sk_A @ sk_B) @ sk_F_2 @ 
% 25.73/25.92         sk_E_2))
% 25.73/25.92         <= (((r2_hidden @ sk_A @ sk_E_2)) & ((r2_hidden @ sk_B @ sk_F_2)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['62', '66'])).
% 25.73/25.92  thf('68', plain,
% 25.73/25.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 25.73/25.92         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 25.73/25.92          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 25.73/25.92      inference('simplify', [status(thm)], ['33'])).
% 25.73/25.92  thf('69', plain,
% 25.73/25.92      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ sk_A @ sk_E_2)) & ((r2_hidden @ sk_B @ sk_F_2)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['67', '68'])).
% 25.73/25.92  thf('70', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G)
% 25.73/25.92        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.73/25.92  thf('71', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G)) <= (((r2_hidden @ sk_C @ sk_G)))),
% 25.73/25.92      inference('split', [status(esa)], ['70'])).
% 25.73/25.92  thf('72', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 25.73/25.92         (~ (r2_hidden @ X1 @ X3)
% 25.73/25.92          | ~ (r2_hidden @ X0 @ X5)
% 25.73/25.92          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 25.73/25.92      inference('simplify', [status(thm)], ['27'])).
% 25.73/25.92  thf('73', plain,
% 25.73/25.92      ((![X0 : $i, X1 : $i]:
% 25.73/25.92          ((zip_tseitin_0 @ sk_C @ X1 @ (k4_tarski @ X1 @ sk_C) @ sk_G @ X0)
% 25.73/25.92           | ~ (r2_hidden @ X1 @ X0)))
% 25.73/25.92         <= (((r2_hidden @ sk_C @ sk_G)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['71', '72'])).
% 25.73/25.92  thf('74', plain,
% 25.73/25.92      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ sk_G @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ sk_A @ sk_E_2)) & 
% 25.73/25.92             ((r2_hidden @ sk_B @ sk_F_2)) & 
% 25.73/25.92             ((r2_hidden @ sk_C @ sk_G)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['69', '73'])).
% 25.73/25.92  thf('75', plain,
% 25.73/25.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.73/25.92         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 25.73/25.92           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.73/25.92  thf('76', plain,
% 25.73/25.92      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_G @ 
% 25.73/25.92         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 25.73/25.92         <= (((r2_hidden @ sk_A @ sk_E_2)) & 
% 25.73/25.92             ((r2_hidden @ sk_B @ sk_F_2)) & 
% 25.73/25.92             ((r2_hidden @ sk_C @ sk_G)))),
% 25.73/25.92      inference('demod', [status(thm)], ['74', '75'])).
% 25.73/25.92  thf('77', plain,
% 25.73/25.92      (((r2_hidden @ sk_A @ sk_E_2)) | 
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['2'])).
% 25.73/25.92  thf('78', plain, (((r2_hidden @ sk_A @ sk_E_2))),
% 25.73/25.92      inference('sat_resolution*', [status(thm)],
% 25.73/25.92                ['41', '46', '55', '58', '59', '77'])).
% 25.73/25.92  thf('79', plain,
% 25.73/25.92      (((r2_hidden @ sk_B @ sk_F_2)) | 
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['63'])).
% 25.73/25.92  thf('80', plain, (((r2_hidden @ sk_B @ sk_F_2))),
% 25.73/25.92      inference('sat_resolution*', [status(thm)],
% 25.73/25.92                ['41', '46', '55', '58', '59', '79'])).
% 25.73/25.92  thf('81', plain,
% 25.73/25.92      (((r2_hidden @ sk_C @ sk_G)) | 
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['70'])).
% 25.73/25.92  thf('82', plain, (((r2_hidden @ sk_C @ sk_G))),
% 25.73/25.92      inference('sat_resolution*', [status(thm)],
% 25.73/25.92                ['41', '46', '55', '58', '59', '81'])).
% 25.73/25.92  thf('83', plain,
% 25.73/25.92      ((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 25.73/25.92        (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_G @ 
% 25.73/25.92        (k2_zfmisc_1 @ sk_E_2 @ sk_F_2))),
% 25.73/25.92      inference('simpl_trail', [status(thm)], ['76', '78', '80', '82'])).
% 25.73/25.92  thf('84', plain,
% 25.73/25.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 25.73/25.92         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 25.73/25.92          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 25.73/25.92      inference('simplify', [status(thm)], ['33'])).
% 25.73/25.92  thf('85', plain,
% 25.73/25.92      ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E_2 @ sk_F_2) @ sk_G))),
% 25.73/25.92      inference('sup-', [status(thm)], ['83', '84'])).
% 25.73/25.92  thf('86', plain,
% 25.73/25.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.73/25.92         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 25.73/25.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 25.73/25.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.73/25.92  thf('87', plain,
% 25.73/25.92      ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 25.73/25.92      inference('demod', [status(thm)], ['85', '86'])).
% 25.73/25.92  thf('88', plain,
% 25.73/25.92      (((r2_hidden @ sk_D_1 @ sk_H)
% 25.73/25.92        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.73/25.92  thf('89', plain,
% 25.73/25.92      (((r2_hidden @ sk_D_1 @ sk_H)) <= (((r2_hidden @ sk_D_1 @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['88'])).
% 25.73/25.92  thf('90', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 25.73/25.92         (~ (r2_hidden @ X1 @ X3)
% 25.73/25.92          | ~ (r2_hidden @ X0 @ X5)
% 25.73/25.92          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 25.73/25.92      inference('simplify', [status(thm)], ['27'])).
% 25.73/25.92  thf('91', plain,
% 25.73/25.92      ((![X0 : $i, X1 : $i]:
% 25.73/25.92          ((zip_tseitin_0 @ sk_D_1 @ X1 @ (k4_tarski @ X1 @ sk_D_1) @ sk_H @ X0)
% 25.73/25.92           | ~ (r2_hidden @ X1 @ X0)))
% 25.73/25.92         <= (((r2_hidden @ sk_D_1 @ sk_H)))),
% 25.73/25.92      inference('sup-', [status(thm)], ['89', '90'])).
% 25.73/25.92  thf('92', plain,
% 25.73/25.92      (((r2_hidden @ sk_D_1 @ sk_H)) | 
% 25.73/25.92       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 25.73/25.92      inference('split', [status(esa)], ['88'])).
% 25.73/25.92  thf('93', plain, (((r2_hidden @ sk_D_1 @ sk_H))),
% 25.73/25.92      inference('sat_resolution*', [status(thm)],
% 25.73/25.92                ['41', '46', '55', '58', '59', '92'])).
% 25.73/25.92  thf('94', plain,
% 25.73/25.92      (![X0 : $i, X1 : $i]:
% 25.73/25.92         ((zip_tseitin_0 @ sk_D_1 @ X1 @ (k4_tarski @ X1 @ sk_D_1) @ sk_H @ X0)
% 25.73/25.92          | ~ (r2_hidden @ X1 @ X0))),
% 25.73/25.92      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 25.73/25.92  thf('95', plain,
% 25.73/25.92      ((zip_tseitin_0 @ sk_D_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92        (k4_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ sk_H @ 
% 25.73/25.92        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 25.73/25.92      inference('sup-', [status(thm)], ['87', '94'])).
% 25.73/25.92  thf('96', plain,
% 25.73/25.92      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 25.73/25.92         ((k4_mcart_1 @ X26 @ X27 @ X28 @ X29)
% 25.73/25.92           = (k4_tarski @ (k3_mcart_1 @ X26 @ X27 @ X28) @ X29))),
% 25.73/25.92      inference('demod', [status(thm)], ['12', '13'])).
% 25.73/25.92  thf('97', plain,
% 25.73/25.92      ((zip_tseitin_0 @ sk_D_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.73/25.92        (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ sk_H @ 
% 25.73/25.92        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 25.73/25.92      inference('demod', [status(thm)], ['95', '96'])).
% 25.73/25.92  thf('98', plain,
% 25.73/25.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 25.73/25.92         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 25.73/25.92          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 25.73/25.92      inference('simplify', [status(thm)], ['33'])).
% 25.73/25.92  thf('99', plain,
% 25.73/25.92      ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G) @ sk_H))),
% 25.73/25.92      inference('sup-', [status(thm)], ['97', '98'])).
% 25.73/25.92  thf('100', plain,
% 25.73/25.92      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.73/25.92         ((k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25)
% 25.73/25.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X22 @ X23 @ X24) @ X25))),
% 25.73/25.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 25.73/25.92  thf('101', plain,
% 25.73/25.92      ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D_1) @ 
% 25.73/25.92        (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))),
% 25.73/25.92      inference('demod', [status(thm)], ['99', '100'])).
% 25.73/25.92  thf('102', plain, ($false), inference('demod', [status(thm)], ['61', '101'])).
% 25.73/25.92  
% 25.73/25.92  % SZS output end Refutation
% 25.73/25.92  
% 25.73/25.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
