%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mwKUZql12u

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:17 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  151 (1682 expanded)
%              Number of leaves         :   30 ( 470 expanded)
%              Depth                    :   28
%              Number of atoms          : 1497 (20226 expanded)
%              Number of equality atoms :   41 (1007 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    | ~ ( r2_hidden @ sk_C_1 @ sk_G )
    | ~ ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_mcart_1 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_tarski @ ( k3_mcart_1 @ X27 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( X7
       != ( k4_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

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

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['19'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup+',[status(thm)],['18','24'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_zfmisc_1 @ X24 @ X25 @ X26 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) ) @ sk_F_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_F_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_F_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) ) @ sk_E_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_E_2 )
   <= ~ ( r2_hidden @ sk_A @ sk_E_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_zfmisc_1 @ X24 @ X25 @ X26 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ) ) @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_G )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['55','56','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_G )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_G )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_mcart_1 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_tarski @ ( k3_mcart_1 @ X27 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['19'])).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('68',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ) @ sk_H )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
   <= ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_H )
   <= ~ ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) )
    | ~ ( r2_hidden @ sk_B @ sk_F_2 )
    | ~ ( r2_hidden @ sk_A @ sk_E_2 )
    | ~ ( r2_hidden @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference('sat_resolution*',[status(thm)],['43','50','62','73','74'])).

thf('76',plain,(
    ~ ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
   <= ( r2_hidden @ sk_A @ sk_E_2 ) ),
    inference(split,[status(esa)],['19'])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ sk_E_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['19'])).

thf('79',plain,(
    r2_hidden @ sk_A @ sk_E_2 ),
    inference('sat_resolution*',[status(thm)],['43','50','62','73','74','78'])).

thf('80',plain,(
    r2_hidden @ sk_A @ sk_E_2 ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
   <= ( r2_hidden @ sk_B @ sk_F_2 ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( r2_hidden @ sk_B @ sk_F_2 )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,(
    r2_hidden @ sk_B @ sk_F_2 ),
    inference('sat_resolution*',[status(thm)],['43','50','62','73','74','83'])).

thf('85',plain,(
    r2_hidden @ sk_B @ sk_F_2 ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 @ ( k4_tarski @ X1 @ sk_B ) @ sk_F_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    zip_tseitin_0 @ sk_B @ sk_A @ ( k4_tarski @ sk_A @ sk_B ) @ sk_F_2 @ sk_E_2 ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('90',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_G )
   <= ( r2_hidden @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_G )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['91'])).

thf('94',plain,(
    r2_hidden @ sk_C_1 @ sk_G ),
    inference('sat_resolution*',[status(thm)],['43','50','62','73','74','93'])).

thf('95',plain,(
    r2_hidden @ sk_C_1 @ sk_G ),
    inference(simpl_trail,[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 @ ( k4_tarski @ X1 @ sk_C_1 ) @ sk_G @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    zip_tseitin_0 @ sk_C_1 @ ( k4_tarski @ sk_A @ sk_B ) @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('100',plain,(
    zip_tseitin_0 @ sk_C_1 @ ( k4_tarski @ sk_A @ sk_B ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_G @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('102',plain,(
    r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E_2 @ sk_F_2 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_zfmisc_1 @ X24 @ X25 @ X26 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('104',plain,(
    r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
   <= ( r2_hidden @ sk_D_1 @ sk_H ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_H )
    | ( r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ) ),
    inference(split,[status(esa)],['105'])).

thf('108',plain,(
    r2_hidden @ sk_D_1 @ sk_H ),
    inference('sat_resolution*',[status(thm)],['43','50','62','73','74','107'])).

thf('109',plain,(
    r2_hidden @ sk_D_1 @ sk_H ),
    inference(simpl_trail,[status(thm)],['106','108'])).

thf('110',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ ( k4_tarski @ X1 @ sk_D_1 ) @ sk_H @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    zip_tseitin_0 @ sk_D_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k4_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 ) @ sk_H @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_mcart_1 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_tarski @ ( k3_mcart_1 @ X27 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('114',plain,(
    zip_tseitin_0 @ sk_D_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ sk_H @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('116',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G ) @ sk_H ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('118',plain,(
    r2_hidden @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['76','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mwKUZql12u
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.46/2.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.46/2.69  % Solved by: fo/fo7.sh
% 2.46/2.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.46/2.69  % done 1884 iterations in 2.232s
% 2.46/2.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.46/2.69  % SZS output start Refutation
% 2.46/2.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.46/2.69  thf(sk_H_type, type, sk_H: $i).
% 2.46/2.69  thf(sk_B_type, type, sk_B: $i).
% 2.46/2.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.46/2.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.46/2.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.46/2.69  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.46/2.69  thf(sk_E_2_type, type, sk_E_2: $i).
% 2.46/2.69  thf(sk_F_2_type, type, sk_F_2: $i).
% 2.46/2.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.46/2.69  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 2.46/2.69  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.46/2.69  thf(sk_G_type, type, sk_G: $i).
% 2.46/2.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.46/2.69  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 2.46/2.69  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.46/2.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.46/2.69  thf(sk_A_type, type, sk_A: $i).
% 2.46/2.69  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.46/2.69  thf(t84_mcart_1, conjecture,
% 2.46/2.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 2.46/2.69     ( ( r2_hidden @
% 2.46/2.69         ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 2.46/2.69       ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 2.46/2.69         ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ))).
% 2.46/2.69  thf(zf_stmt_0, negated_conjecture,
% 2.46/2.69    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 2.46/2.69        ( ( r2_hidden @
% 2.46/2.69            ( k4_mcart_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) <=>
% 2.46/2.69          ( ( r2_hidden @ A @ E ) & ( r2_hidden @ B @ F ) & 
% 2.46/2.69            ( r2_hidden @ C @ G ) & ( r2_hidden @ D @ H ) ) ) )),
% 2.46/2.69    inference('cnf.neg', [status(esa)], [t84_mcart_1])).
% 2.46/2.69  thf('0', plain,
% 2.46/2.69      ((~ (r2_hidden @ sk_D_1 @ sk_H)
% 2.46/2.69        | ~ (r2_hidden @ sk_C_1 @ sk_G)
% 2.46/2.69        | ~ (r2_hidden @ sk_B @ sk_F_2)
% 2.46/2.69        | ~ (r2_hidden @ sk_A @ sk_E_2)
% 2.46/2.69        | ~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69             (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('1', plain,
% 2.46/2.69      ((~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 2.46/2.69         <= (~
% 2.46/2.69             ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf(d4_mcart_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i,D:$i]:
% 2.46/2.69     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 2.46/2.69       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 2.46/2.69  thf('2', plain,
% 2.46/2.69      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.46/2.69         ((k4_mcart_1 @ X27 @ X28 @ X29 @ X30)
% 2.46/2.69           = (k4_tarski @ (k3_mcart_1 @ X27 @ X28 @ X29) @ X30))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_mcart_1])).
% 2.46/2.69  thf(d1_tarski, axiom,
% 2.46/2.69    (![A:$i,B:$i]:
% 2.46/2.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.46/2.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.46/2.69  thf('3', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 2.46/2.69      inference('cnf', [status(esa)], [d1_tarski])).
% 2.46/2.69  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.46/2.69      inference('simplify', [status(thm)], ['3'])).
% 2.46/2.69  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.46/2.69      inference('simplify', [status(thm)], ['3'])).
% 2.46/2.69  thf(d2_zfmisc_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i]:
% 2.46/2.69     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.46/2.69       ( ![D:$i]:
% 2.46/2.69         ( ( r2_hidden @ D @ C ) <=>
% 2.46/2.69           ( ?[E:$i,F:$i]:
% 2.46/2.69             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.46/2.69               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.46/2.69  thf(zf_stmt_1, axiom,
% 2.46/2.69    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.46/2.69     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.46/2.69       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.46/2.69         ( r2_hidden @ E @ A ) ) ))).
% 2.46/2.69  thf('6', plain,
% 2.46/2.69      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 2.46/2.69         ((zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10)
% 2.46/2.69          | ~ (r2_hidden @ X5 @ X10)
% 2.46/2.69          | ~ (r2_hidden @ X6 @ X8)
% 2.46/2.69          | ((X7) != (k4_tarski @ X5 @ X6)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.46/2.69  thf('7', plain,
% 2.46/2.69      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X6 @ X8)
% 2.46/2.69          | ~ (r2_hidden @ X5 @ X10)
% 2.46/2.69          | (zip_tseitin_0 @ X6 @ X5 @ (k4_tarski @ X5 @ X6) @ X8 @ X10))),
% 2.46/2.69      inference('simplify', [status(thm)], ['6'])).
% 2.46/2.69  thf('8', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((zip_tseitin_0 @ X0 @ X2 @ (k4_tarski @ X2 @ X0) @ 
% 2.46/2.69           (k1_tarski @ X0) @ X1)
% 2.46/2.69          | ~ (r2_hidden @ X2 @ X1))),
% 2.46/2.69      inference('sup-', [status(thm)], ['5', '7'])).
% 2.46/2.69  thf('9', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 2.46/2.69          (k1_tarski @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['4', '8'])).
% 2.46/2.69  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.46/2.69  thf(zf_stmt_3, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i]:
% 2.46/2.69     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.46/2.69       ( ![D:$i]:
% 2.46/2.69         ( ( r2_hidden @ D @ C ) <=>
% 2.46/2.69           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.46/2.69  thf('10', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.46/2.69         (~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15)
% 2.46/2.69          | (r2_hidden @ X13 @ X16)
% 2.46/2.69          | ((X16) != (k2_zfmisc_1 @ X15 @ X14)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.69  thf('11', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.46/2.69         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 2.46/2.69          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 2.46/2.69      inference('simplify', [status(thm)], ['10'])).
% 2.46/2.69  thf('12', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 2.46/2.69          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['9', '11'])).
% 2.46/2.69  thf(t10_mcart_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i]:
% 2.46/2.69     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 2.46/2.69       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 2.46/2.69         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 2.46/2.69  thf('13', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('14', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X1 @ X0)) @ (k1_tarski @ X1))),
% 2.46/2.69      inference('sup-', [status(thm)], ['12', '13'])).
% 2.46/2.69  thf('15', plain,
% 2.46/2.69      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 2.46/2.69      inference('cnf', [status(esa)], [d1_tarski])).
% 2.46/2.69  thf('16', plain,
% 2.46/2.69      (![X0 : $i, X3 : $i]:
% 2.46/2.69         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['15'])).
% 2.46/2.69  thf('17', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X0 @ X1)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['14', '16'])).
% 2.46/2.69  thf('18', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.69           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['2', '17'])).
% 2.46/2.69  thf('19', plain,
% 2.46/2.69      (((r2_hidden @ sk_A @ sk_E_2)
% 2.46/2.69        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('20', plain,
% 2.46/2.69      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('split', [status(esa)], ['19'])).
% 2.46/2.69  thf(d4_zfmisc_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i,D:$i]:
% 2.46/2.69     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 2.46/2.69       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 2.46/2.69  thf('21', plain,
% 2.46/2.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.46/2.69         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 2.46/2.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.46/2.69  thf('22', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('23', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.69          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['21', '22'])).
% 2.46/2.69  thf('24', plain,
% 2.46/2.69      (((r2_hidden @ 
% 2.46/2.69         (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)) @ 
% 2.46/2.69         (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['20', '23'])).
% 2.46/2.69  thf('25', plain,
% 2.46/2.69      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.46/2.69         (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup+', [status(thm)], ['18', '24'])).
% 2.46/2.69  thf(d3_zfmisc_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i]:
% 2.46/2.69     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 2.46/2.69       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 2.46/2.69  thf('26', plain,
% 2.46/2.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.46/2.69         ((k3_zfmisc_1 @ X24 @ X25 @ X26)
% 2.46/2.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25) @ X26))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.69  thf('27', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('28', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.46/2.69          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['26', '27'])).
% 2.46/2.69  thf('29', plain,
% 2.46/2.69      (((r2_hidden @ (k1_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 2.46/2.69         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['25', '28'])).
% 2.46/2.69  thf(d3_mcart_1, axiom,
% 2.46/2.69    (![A:$i,B:$i,C:$i]:
% 2.46/2.69     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.46/2.69  thf('30', plain,
% 2.46/2.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.46/2.69         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.46/2.69           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.69  thf('31', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X0 @ X1)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['14', '16'])).
% 2.46/2.69  thf('32', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['30', '31'])).
% 2.46/2.69  thf('33', plain,
% 2.46/2.69      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 2.46/2.69         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('demod', [status(thm)], ['29', '32'])).
% 2.46/2.69  thf('34', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('35', plain,
% 2.46/2.69      (((r2_hidden @ (k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) @ sk_F_2))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['33', '34'])).
% 2.46/2.69  thf('36', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 2.46/2.69          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['9', '11'])).
% 2.46/2.69  thf('37', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('38', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X1 @ X0)) @ (k1_tarski @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['36', '37'])).
% 2.46/2.69  thf('39', plain,
% 2.46/2.69      (![X0 : $i, X3 : $i]:
% 2.46/2.69         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.46/2.69      inference('simplify', [status(thm)], ['15'])).
% 2.46/2.69  thf('40', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['38', '39'])).
% 2.46/2.69  thf('41', plain,
% 2.46/2.69      (((r2_hidden @ sk_B @ sk_F_2))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('demod', [status(thm)], ['35', '40'])).
% 2.46/2.69  thf('42', plain,
% 2.46/2.69      ((~ (r2_hidden @ sk_B @ sk_F_2)) <= (~ ((r2_hidden @ sk_B @ sk_F_2)))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf('43', plain,
% 2.46/2.69      (((r2_hidden @ sk_B @ sk_F_2)) | 
% 2.46/2.69       ~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['41', '42'])).
% 2.46/2.69  thf('44', plain,
% 2.46/2.69      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 2.46/2.69         (k2_zfmisc_1 @ sk_E_2 @ sk_F_2)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('demod', [status(thm)], ['29', '32'])).
% 2.46/2.69  thf('45', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('46', plain,
% 2.46/2.69      (((r2_hidden @ (k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) @ sk_E_2))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['44', '45'])).
% 2.46/2.69  thf('47', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X0 @ X1)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['14', '16'])).
% 2.46/2.69  thf('48', plain,
% 2.46/2.69      (((r2_hidden @ sk_A @ sk_E_2))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('demod', [status(thm)], ['46', '47'])).
% 2.46/2.69  thf('49', plain,
% 2.46/2.69      ((~ (r2_hidden @ sk_A @ sk_E_2)) <= (~ ((r2_hidden @ sk_A @ sk_E_2)))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf('50', plain,
% 2.46/2.69      (((r2_hidden @ sk_A @ sk_E_2)) | 
% 2.46/2.69       ~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['48', '49'])).
% 2.46/2.69  thf('51', plain,
% 2.46/2.69      (((r2_hidden @ 
% 2.46/2.69         (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)) @ 
% 2.46/2.69         (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['20', '23'])).
% 2.46/2.69  thf('52', plain,
% 2.46/2.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.46/2.69         ((k3_zfmisc_1 @ X24 @ X25 @ X26)
% 2.46/2.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25) @ X26))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.69  thf('53', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('54', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.46/2.69          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['52', '53'])).
% 2.46/2.69  thf('55', plain,
% 2.46/2.69      (((r2_hidden @ 
% 2.46/2.69         (k2_mcart_1 @ 
% 2.46/2.69          (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))) @ 
% 2.46/2.69         sk_G))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['51', '54'])).
% 2.46/2.69  thf('56', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.69           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 2.46/2.69      inference('sup+', [status(thm)], ['2', '17'])).
% 2.46/2.69  thf('57', plain,
% 2.46/2.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.46/2.69         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.46/2.69           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.69  thf('58', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['38', '39'])).
% 2.46/2.69  thf('59', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.69         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 2.46/2.69      inference('sup+', [status(thm)], ['57', '58'])).
% 2.46/2.69  thf('60', plain,
% 2.46/2.69      (((r2_hidden @ sk_C_1 @ sk_G))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('demod', [status(thm)], ['55', '56', '59'])).
% 2.46/2.69  thf('61', plain,
% 2.46/2.69      ((~ (r2_hidden @ sk_C_1 @ sk_G)) <= (~ ((r2_hidden @ sk_C_1 @ sk_G)))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf('62', plain,
% 2.46/2.69      (((r2_hidden @ sk_C_1 @ sk_G)) | 
% 2.46/2.69       ~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['60', '61'])).
% 2.46/2.69  thf('63', plain,
% 2.46/2.69      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.46/2.69         ((k4_mcart_1 @ X27 @ X28 @ X29 @ X30)
% 2.46/2.69           = (k4_tarski @ (k3_mcart_1 @ X27 @ X28 @ X29) @ X30))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_mcart_1])).
% 2.46/2.69  thf('64', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['38', '39'])).
% 2.46/2.69  thf('65', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.69         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 2.46/2.69      inference('sup+', [status(thm)], ['63', '64'])).
% 2.46/2.69  thf('66', plain,
% 2.46/2.69      (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('split', [status(esa)], ['19'])).
% 2.46/2.69  thf('67', plain,
% 2.46/2.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.46/2.69         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 2.46/2.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.46/2.69  thf('68', plain,
% 2.46/2.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.69         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 2.46/2.69          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 2.46/2.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.46/2.69  thf('69', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.69          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['67', '68'])).
% 2.46/2.69  thf('70', plain,
% 2.46/2.69      (((r2_hidden @ 
% 2.46/2.69         (k2_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)) @ sk_H))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup-', [status(thm)], ['66', '69'])).
% 2.46/2.69  thf('71', plain,
% 2.46/2.69      (((r2_hidden @ sk_D_1 @ sk_H))
% 2.46/2.69         <= (((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69               (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))))),
% 2.46/2.69      inference('sup+', [status(thm)], ['65', '70'])).
% 2.46/2.69  thf('72', plain,
% 2.46/2.69      ((~ (r2_hidden @ sk_D_1 @ sk_H)) <= (~ ((r2_hidden @ sk_D_1 @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf('73', plain,
% 2.46/2.69      (((r2_hidden @ sk_D_1 @ sk_H)) | 
% 2.46/2.69       ~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('sup-', [status(thm)], ['71', '72'])).
% 2.46/2.69  thf('74', plain,
% 2.46/2.69      (~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))) | 
% 2.46/2.69       ~ ((r2_hidden @ sk_B @ sk_F_2)) | ~ ((r2_hidden @ sk_A @ sk_E_2)) | 
% 2.46/2.69       ~ ((r2_hidden @ sk_D_1 @ sk_H)) | ~ ((r2_hidden @ sk_C_1 @ sk_G))),
% 2.46/2.69      inference('split', [status(esa)], ['0'])).
% 2.46/2.69  thf('75', plain,
% 2.46/2.69      (~
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('sat_resolution*', [status(thm)],
% 2.46/2.69                ['43', '50', '62', '73', '74'])).
% 2.46/2.69  thf('76', plain,
% 2.46/2.69      (~ (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69          (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))),
% 2.46/2.69      inference('simpl_trail', [status(thm)], ['1', '75'])).
% 2.46/2.69  thf('77', plain,
% 2.46/2.69      (((r2_hidden @ sk_A @ sk_E_2)) <= (((r2_hidden @ sk_A @ sk_E_2)))),
% 2.46/2.69      inference('split', [status(esa)], ['19'])).
% 2.46/2.69  thf('78', plain,
% 2.46/2.69      (((r2_hidden @ sk_A @ sk_E_2)) | 
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['19'])).
% 2.46/2.69  thf('79', plain, (((r2_hidden @ sk_A @ sk_E_2))),
% 2.46/2.69      inference('sat_resolution*', [status(thm)],
% 2.46/2.69                ['43', '50', '62', '73', '74', '78'])).
% 2.46/2.69  thf('80', plain, ((r2_hidden @ sk_A @ sk_E_2)),
% 2.46/2.69      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 2.46/2.69  thf('81', plain,
% 2.46/2.69      (((r2_hidden @ sk_B @ sk_F_2)
% 2.46/2.69        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('82', plain,
% 2.46/2.69      (((r2_hidden @ sk_B @ sk_F_2)) <= (((r2_hidden @ sk_B @ sk_F_2)))),
% 2.46/2.69      inference('split', [status(esa)], ['81'])).
% 2.46/2.69  thf('83', plain,
% 2.46/2.69      (((r2_hidden @ sk_B @ sk_F_2)) | 
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['81'])).
% 2.46/2.69  thf('84', plain, (((r2_hidden @ sk_B @ sk_F_2))),
% 2.46/2.69      inference('sat_resolution*', [status(thm)],
% 2.46/2.69                ['43', '50', '62', '73', '74', '83'])).
% 2.46/2.69  thf('85', plain, ((r2_hidden @ sk_B @ sk_F_2)),
% 2.46/2.69      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 2.46/2.69  thf('86', plain,
% 2.46/2.69      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X6 @ X8)
% 2.46/2.69          | ~ (r2_hidden @ X5 @ X10)
% 2.46/2.69          | (zip_tseitin_0 @ X6 @ X5 @ (k4_tarski @ X5 @ X6) @ X8 @ X10))),
% 2.46/2.69      inference('simplify', [status(thm)], ['6'])).
% 2.46/2.69  thf('87', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((zip_tseitin_0 @ sk_B @ X1 @ (k4_tarski @ X1 @ sk_B) @ sk_F_2 @ X0)
% 2.46/2.69          | ~ (r2_hidden @ X1 @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['85', '86'])).
% 2.46/2.69  thf('88', plain,
% 2.46/2.69      ((zip_tseitin_0 @ sk_B @ sk_A @ (k4_tarski @ sk_A @ sk_B) @ sk_F_2 @ 
% 2.46/2.69        sk_E_2)),
% 2.46/2.69      inference('sup-', [status(thm)], ['80', '87'])).
% 2.46/2.69  thf('89', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.46/2.69         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 2.46/2.69          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 2.46/2.69      inference('simplify', [status(thm)], ['10'])).
% 2.46/2.69  thf('90', plain,
% 2.46/2.69      ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_E_2 @ sk_F_2))),
% 2.46/2.69      inference('sup-', [status(thm)], ['88', '89'])).
% 2.46/2.69  thf('91', plain,
% 2.46/2.69      (((r2_hidden @ sk_C_1 @ sk_G)
% 2.46/2.69        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('92', plain,
% 2.46/2.69      (((r2_hidden @ sk_C_1 @ sk_G)) <= (((r2_hidden @ sk_C_1 @ sk_G)))),
% 2.46/2.69      inference('split', [status(esa)], ['91'])).
% 2.46/2.69  thf('93', plain,
% 2.46/2.69      (((r2_hidden @ sk_C_1 @ sk_G)) | 
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['91'])).
% 2.46/2.69  thf('94', plain, (((r2_hidden @ sk_C_1 @ sk_G))),
% 2.46/2.69      inference('sat_resolution*', [status(thm)],
% 2.46/2.69                ['43', '50', '62', '73', '74', '93'])).
% 2.46/2.69  thf('95', plain, ((r2_hidden @ sk_C_1 @ sk_G)),
% 2.46/2.69      inference('simpl_trail', [status(thm)], ['92', '94'])).
% 2.46/2.69  thf('96', plain,
% 2.46/2.69      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X6 @ X8)
% 2.46/2.69          | ~ (r2_hidden @ X5 @ X10)
% 2.46/2.69          | (zip_tseitin_0 @ X6 @ X5 @ (k4_tarski @ X5 @ X6) @ X8 @ X10))),
% 2.46/2.69      inference('simplify', [status(thm)], ['6'])).
% 2.46/2.69  thf('97', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((zip_tseitin_0 @ sk_C_1 @ X1 @ (k4_tarski @ X1 @ sk_C_1) @ sk_G @ X0)
% 2.46/2.69          | ~ (r2_hidden @ X1 @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['95', '96'])).
% 2.46/2.69  thf('98', plain,
% 2.46/2.69      ((zip_tseitin_0 @ sk_C_1 @ (k4_tarski @ sk_A @ sk_B) @ 
% 2.46/2.69        (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_G @ 
% 2.46/2.69        (k2_zfmisc_1 @ sk_E_2 @ sk_F_2))),
% 2.46/2.69      inference('sup-', [status(thm)], ['90', '97'])).
% 2.46/2.69  thf('99', plain,
% 2.46/2.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.46/2.69         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.46/2.69           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.69  thf('100', plain,
% 2.46/2.69      ((zip_tseitin_0 @ sk_C_1 @ (k4_tarski @ sk_A @ sk_B) @ 
% 2.46/2.69        (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ sk_G @ 
% 2.46/2.69        (k2_zfmisc_1 @ sk_E_2 @ sk_F_2))),
% 2.46/2.69      inference('demod', [status(thm)], ['98', '99'])).
% 2.46/2.69  thf('101', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.46/2.69         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 2.46/2.69          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 2.46/2.69      inference('simplify', [status(thm)], ['10'])).
% 2.46/2.69  thf('102', plain,
% 2.46/2.69      ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.46/2.69        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E_2 @ sk_F_2) @ sk_G))),
% 2.46/2.69      inference('sup-', [status(thm)], ['100', '101'])).
% 2.46/2.69  thf('103', plain,
% 2.46/2.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.46/2.69         ((k3_zfmisc_1 @ X24 @ X25 @ X26)
% 2.46/2.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25) @ X26))),
% 2.46/2.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.69  thf('104', plain,
% 2.46/2.69      ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.46/2.69        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 2.46/2.69      inference('demod', [status(thm)], ['102', '103'])).
% 2.46/2.69  thf('105', plain,
% 2.46/2.69      (((r2_hidden @ sk_D_1 @ sk_H)
% 2.46/2.69        | (r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69           (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.69  thf('106', plain,
% 2.46/2.69      (((r2_hidden @ sk_D_1 @ sk_H)) <= (((r2_hidden @ sk_D_1 @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['105'])).
% 2.46/2.69  thf('107', plain,
% 2.46/2.69      (((r2_hidden @ sk_D_1 @ sk_H)) | 
% 2.46/2.69       ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69         (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H)))),
% 2.46/2.69      inference('split', [status(esa)], ['105'])).
% 2.46/2.69  thf('108', plain, (((r2_hidden @ sk_D_1 @ sk_H))),
% 2.46/2.69      inference('sat_resolution*', [status(thm)],
% 2.46/2.69                ['43', '50', '62', '73', '74', '107'])).
% 2.46/2.69  thf('109', plain, ((r2_hidden @ sk_D_1 @ sk_H)),
% 2.46/2.69      inference('simpl_trail', [status(thm)], ['106', '108'])).
% 2.46/2.69  thf('110', plain,
% 2.46/2.69      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i]:
% 2.46/2.69         (~ (r2_hidden @ X6 @ X8)
% 2.46/2.69          | ~ (r2_hidden @ X5 @ X10)
% 2.46/2.69          | (zip_tseitin_0 @ X6 @ X5 @ (k4_tarski @ X5 @ X6) @ X8 @ X10))),
% 2.46/2.69      inference('simplify', [status(thm)], ['6'])).
% 2.46/2.69  thf('111', plain,
% 2.46/2.69      (![X0 : $i, X1 : $i]:
% 2.46/2.69         ((zip_tseitin_0 @ sk_D_1 @ X1 @ (k4_tarski @ X1 @ sk_D_1) @ sk_H @ X0)
% 2.46/2.69          | ~ (r2_hidden @ X1 @ X0))),
% 2.46/2.69      inference('sup-', [status(thm)], ['109', '110'])).
% 2.46/2.69  thf('112', plain,
% 2.46/2.69      ((zip_tseitin_0 @ sk_D_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.46/2.69        (k4_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1) @ sk_H @ 
% 2.46/2.69        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 2.46/2.69      inference('sup-', [status(thm)], ['104', '111'])).
% 2.46/2.69  thf('113', plain,
% 2.46/2.69      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.46/2.69         ((k4_mcart_1 @ X27 @ X28 @ X29 @ X30)
% 2.46/2.69           = (k4_tarski @ (k3_mcart_1 @ X27 @ X28 @ X29) @ X30))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_mcart_1])).
% 2.46/2.69  thf('114', plain,
% 2.46/2.69      ((zip_tseitin_0 @ sk_D_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.46/2.69        (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ sk_H @ 
% 2.46/2.69        (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G))),
% 2.46/2.69      inference('demod', [status(thm)], ['112', '113'])).
% 2.46/2.69  thf('115', plain,
% 2.46/2.69      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.46/2.69         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 2.46/2.69          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 2.46/2.69      inference('simplify', [status(thm)], ['10'])).
% 2.46/2.69  thf('116', plain,
% 2.46/2.69      ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G) @ sk_H))),
% 2.46/2.69      inference('sup-', [status(thm)], ['114', '115'])).
% 2.46/2.69  thf('117', plain,
% 2.46/2.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.46/2.69         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 2.46/2.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 2.46/2.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.46/2.69  thf('118', plain,
% 2.46/2.69      ((r2_hidden @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 2.46/2.69        (k4_zfmisc_1 @ sk_E_2 @ sk_F_2 @ sk_G @ sk_H))),
% 2.46/2.69      inference('demod', [status(thm)], ['116', '117'])).
% 2.46/2.69  thf('119', plain, ($false), inference('demod', [status(thm)], ['76', '118'])).
% 2.46/2.69  
% 2.46/2.69  % SZS output end Refutation
% 2.46/2.69  
% 2.46/2.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
