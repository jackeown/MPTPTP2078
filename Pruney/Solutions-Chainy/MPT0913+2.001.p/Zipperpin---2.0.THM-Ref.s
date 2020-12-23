%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zz8nu5owop

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:03 EST 2020

% Result     : Theorem 4.86s
% Output     : Refutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 323 expanded)
%              Number of leaves         :   24 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          : 1420 (4907 expanded)
%              Number of equality atoms :   40 ( 161 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    ( ( r2_hidden @ sk_B @ sk_E_2 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_E_2 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_C @ sk_F_2 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_F_2 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_D_1 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_E_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ sk_F_2 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,
    ( ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
      = ( k4_tarski @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('16',plain,(
    ! [X22: $i,X24: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X22 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( ( k2_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
      = ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('19',plain,(
    ! [X22: $i,X24: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X22 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C
      = ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ sk_F_2 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F_2 )
    | ~ ( r2_hidden @ sk_B @ sk_E_2 )
    | ~ ( r2_hidden @ sk_A @ sk_D_1 )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_F_2 )
   <= ~ ( r2_hidden @ sk_C @ sk_F_2 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_C @ sk_F_2 )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
      = ( k4_tarski @ ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) @ ( sk_F_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
      = ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_tarski @ sk_A @ sk_B )
      = ( sk_E_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('38',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ sk_E_2 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,
    ( ( ( k4_tarski @ sk_A @ sk_B )
      = ( k4_tarski @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X22: $i,X24: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X22 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('45',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X24: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X22 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( sk_B
      = ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_E_2 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_E_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_E_2 ) ),
    inference(split,[status(esa)],['23'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ sk_E_2 )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ sk_D_1 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_tarski @ sk_A @ sk_B )
      = ( k4_tarski @ ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) @ ( sk_F_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('58',plain,
    ( ( sk_A
      = ( sk_E_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ sk_D_1 )
   <= ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['23'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_D_1 )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_E_2 )
    | ~ ( r2_hidden @ sk_A @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ sk_F_2 )
    | ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('63',plain,
    ( ( r2_hidden @ sk_A @ sk_D_1 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ sk_D_1 )
   <= ( r2_hidden @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ sk_E_2 )
   <= ( r2_hidden @ sk_B @ sk_E_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X1 @ ( k4_tarski @ X1 @ sk_B ) @ sk_E_2 @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( zip_tseitin_0 @ sk_B @ sk_A @ ( k4_tarski @ sk_A @ sk_B ) @ sk_E_2 @ sk_D_1 )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_C @ sk_F_2 )
   <= ( r2_hidden @ sk_C @ sk_F_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X0 @ X5 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X1 @ ( k4_tarski @ X1 @ sk_C ) @ sk_F_2 @ X0 )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( r2_hidden @ sk_C @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 )
      & ( r2_hidden @ sk_C @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('78',plain,
    ( ( zip_tseitin_0 @ sk_C @ ( k4_tarski @ sk_A @ sk_B ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ sk_F_2 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 )
      & ( r2_hidden @ sk_C @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('80',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) @ sk_F_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 )
      & ( r2_hidden @ sk_C @ sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('82',plain,
    ( ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
   <= ( ( r2_hidden @ sk_A @ sk_D_1 )
      & ( r2_hidden @ sk_B @ sk_E_2 )
      & ( r2_hidden @ sk_C @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
   <= ~ ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_D_1 )
    | ( r2_hidden @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    | ~ ( r2_hidden @ sk_C @ sk_F_2 )
    | ~ ( r2_hidden @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','25','50','61','62','63','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zz8nu5owop
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.86/5.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.86/5.06  % Solved by: fo/fo7.sh
% 4.86/5.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.86/5.06  % done 1658 iterations in 4.583s
% 4.86/5.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.86/5.06  % SZS output start Refutation
% 4.86/5.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.86/5.06  thf(sk_F_2_type, type, sk_F_2: $i).
% 4.86/5.06  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 4.86/5.06  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.86/5.06  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 4.86/5.06  thf(sk_C_type, type, sk_C: $i).
% 4.86/5.06  thf(sk_B_type, type, sk_B: $i).
% 4.86/5.06  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.86/5.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.86/5.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 4.86/5.06  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 4.86/5.06  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 4.86/5.06  thf(sk_E_2_type, type, sk_E_2: $i).
% 4.86/5.06  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 4.86/5.06  thf(sk_A_type, type, sk_A: $i).
% 4.86/5.06  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 4.86/5.06  thf(t73_mcart_1, conjecture,
% 4.86/5.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.86/5.06     ( ( r2_hidden @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 4.86/5.06       ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & ( r2_hidden @ C @ F ) ) ))).
% 4.86/5.06  thf(zf_stmt_0, negated_conjecture,
% 4.86/5.06    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.86/5.06        ( ( r2_hidden @
% 4.86/5.06            ( k3_mcart_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) <=>
% 4.86/5.06          ( ( r2_hidden @ A @ D ) & ( r2_hidden @ B @ E ) & 
% 4.86/5.06            ( r2_hidden @ C @ F ) ) ) )),
% 4.86/5.06    inference('cnf.neg', [status(esa)], [t73_mcart_1])).
% 4.86/5.06  thf('0', plain,
% 4.86/5.06      (((r2_hidden @ sk_B @ sk_E_2)
% 4.86/5.06        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06           (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.06  thf('1', plain,
% 4.86/5.06      (((r2_hidden @ sk_B @ sk_E_2)) | 
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['0'])).
% 4.86/5.06  thf('2', plain,
% 4.86/5.06      (((r2_hidden @ sk_C @ sk_F_2)
% 4.86/5.06        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06           (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.06  thf('3', plain,
% 4.86/5.06      (((r2_hidden @ sk_C @ sk_F_2)) | 
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['2'])).
% 4.86/5.06  thf('4', plain,
% 4.86/5.06      (((r2_hidden @ sk_A @ sk_D_1)
% 4.86/5.06        | (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06           (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.06  thf('5', plain,
% 4.86/5.06      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('split', [status(esa)], ['4'])).
% 4.86/5.06  thf(d3_zfmisc_1, axiom,
% 4.86/5.06    (![A:$i,B:$i,C:$i]:
% 4.86/5.06     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 4.86/5.06       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 4.86/5.06  thf('6', plain,
% 4.86/5.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.06         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 4.86/5.06           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 4.86/5.06      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.86/5.06  thf(d2_zfmisc_1, axiom,
% 4.86/5.06    (![A:$i,B:$i,C:$i]:
% 4.86/5.06     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 4.86/5.06       ( ![D:$i]:
% 4.86/5.06         ( ( r2_hidden @ D @ C ) <=>
% 4.86/5.06           ( ?[E:$i,F:$i]:
% 4.86/5.06             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 4.86/5.06               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 4.86/5.06  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 4.86/5.06  thf(zf_stmt_2, axiom,
% 4.86/5.06    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 4.86/5.06     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 4.86/5.06       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 4.86/5.06         ( r2_hidden @ E @ A ) ) ))).
% 4.86/5.06  thf(zf_stmt_3, axiom,
% 4.86/5.06    (![A:$i,B:$i,C:$i]:
% 4.86/5.06     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 4.86/5.06       ( ![D:$i]:
% 4.86/5.06         ( ( r2_hidden @ D @ C ) <=>
% 4.86/5.06           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 4.86/5.06  thf('7', plain,
% 4.86/5.06      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.86/5.06         (~ (r2_hidden @ X12 @ X11)
% 4.86/5.06          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 4.86/5.06             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 4.86/5.06          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.86/5.06  thf('8', plain,
% 4.86/5.06      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.86/5.06         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 4.86/5.06           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 4.86/5.06          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 4.86/5.06      inference('simplify', [status(thm)], ['7'])).
% 4.86/5.06  thf('9', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.86/5.06         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 4.86/5.06          | (zip_tseitin_0 @ (sk_F_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 4.86/5.06             (sk_E_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X3 @ X0 @ 
% 4.86/5.06             (k2_zfmisc_1 @ X2 @ X1)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['6', '8'])).
% 4.86/5.06  thf('10', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['5', '9'])).
% 4.86/5.06  thf('11', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('12', plain,
% 4.86/5.06      (((r2_hidden @ 
% 4.86/5.06         (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         sk_F_2))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['10', '11'])).
% 4.86/5.06  thf('13', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['5', '9'])).
% 4.86/5.06  thf('14', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         (((X2) = (k4_tarski @ X0 @ X1))
% 4.86/5.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('15', plain,
% 4.86/5.06      ((((k3_mcart_1 @ sk_A @ sk_B @ sk_C)
% 4.86/5.06          = (k4_tarski @ 
% 4.86/5.06             (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06              (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06             (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06              (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['13', '14'])).
% 4.86/5.06  thf(t7_mcart_1, axiom,
% 4.86/5.06    (![A:$i,B:$i]:
% 4.86/5.06     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 4.86/5.06       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 4.86/5.06  thf('16', plain,
% 4.86/5.06      (![X22 : $i, X24 : $i]: ((k2_mcart_1 @ (k4_tarski @ X22 @ X24)) = (X24))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('17', plain,
% 4.86/5.06      ((((k2_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 4.86/5.06          = (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06             (k2_zfmisc_1 @ sk_D_1 @ sk_E_2))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup+', [status(thm)], ['15', '16'])).
% 4.86/5.06  thf(d3_mcart_1, axiom,
% 4.86/5.06    (![A:$i,B:$i,C:$i]:
% 4.86/5.06     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 4.86/5.06  thf('18', plain,
% 4.86/5.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.86/5.06         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 4.86/5.06           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 4.86/5.06      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.86/5.06  thf('19', plain,
% 4.86/5.06      (![X22 : $i, X24 : $i]: ((k2_mcart_1 @ (k4_tarski @ X22 @ X24)) = (X24))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('20', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.06         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 4.86/5.06      inference('sup+', [status(thm)], ['18', '19'])).
% 4.86/5.06  thf('21', plain,
% 4.86/5.06      ((((sk_C)
% 4.86/5.06          = (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06             (k2_zfmisc_1 @ sk_D_1 @ sk_E_2))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['17', '20'])).
% 4.86/5.06  thf('22', plain,
% 4.86/5.06      (((r2_hidden @ sk_C @ sk_F_2))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['12', '21'])).
% 4.86/5.06  thf('23', plain,
% 4.86/5.06      ((~ (r2_hidden @ sk_C @ sk_F_2)
% 4.86/5.06        | ~ (r2_hidden @ sk_B @ sk_E_2)
% 4.86/5.06        | ~ (r2_hidden @ sk_A @ sk_D_1)
% 4.86/5.06        | ~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06             (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.06  thf('24', plain,
% 4.86/5.06      ((~ (r2_hidden @ sk_C @ sk_F_2)) <= (~ ((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['23'])).
% 4.86/5.06  thf('25', plain,
% 4.86/5.06      (((r2_hidden @ sk_C @ sk_F_2)) | 
% 4.86/5.06       ~
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['22', '24'])).
% 4.86/5.06  thf('26', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['5', '9'])).
% 4.86/5.06  thf('27', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         ((r2_hidden @ X0 @ X4) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('28', plain,
% 4.86/5.06      (((r2_hidden @ 
% 4.86/5.06         (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06          (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['26', '27'])).
% 4.86/5.06  thf('29', plain,
% 4.86/5.06      ((((k3_mcart_1 @ sk_A @ sk_B @ sk_C)
% 4.86/5.06          = (k4_tarski @ 
% 4.86/5.06             (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06              (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) @ 
% 4.86/5.06             (sk_F_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06              (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['13', '14'])).
% 4.86/5.06  thf('30', plain,
% 4.86/5.06      (![X22 : $i, X23 : $i]: ((k1_mcart_1 @ (k4_tarski @ X22 @ X23)) = (X22))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('31', plain,
% 4.86/5.06      ((((k1_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 4.86/5.06          = (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06             (k2_zfmisc_1 @ sk_D_1 @ sk_E_2))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup+', [status(thm)], ['29', '30'])).
% 4.86/5.06  thf('32', plain,
% 4.86/5.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.86/5.06         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 4.86/5.06           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 4.86/5.06      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.86/5.06  thf('33', plain,
% 4.86/5.06      (![X22 : $i, X23 : $i]: ((k1_mcart_1 @ (k4_tarski @ X22 @ X23)) = (X22))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('34', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.06         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 4.86/5.06      inference('sup+', [status(thm)], ['32', '33'])).
% 4.86/5.06  thf('35', plain,
% 4.86/5.06      ((((k4_tarski @ sk_A @ sk_B)
% 4.86/5.06          = (sk_E_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06             (k2_zfmisc_1 @ sk_D_1 @ sk_E_2))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['31', '34'])).
% 4.86/5.06  thf('36', plain,
% 4.86/5.06      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['28', '35'])).
% 4.86/5.06  thf('37', plain,
% 4.86/5.06      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.86/5.06         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 4.86/5.06           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 4.86/5.06          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 4.86/5.06      inference('simplify', [status(thm)], ['7'])).
% 4.86/5.06  thf('38', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['36', '37'])).
% 4.86/5.06  thf('39', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('40', plain,
% 4.86/5.06      (((r2_hidden @ (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         sk_E_2))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['38', '39'])).
% 4.86/5.06  thf('41', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['36', '37'])).
% 4.86/5.06  thf('42', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         (((X2) = (k4_tarski @ X0 @ X1))
% 4.86/5.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('43', plain,
% 4.86/5.06      ((((k4_tarski @ sk_A @ sk_B)
% 4.86/5.06          = (k4_tarski @ 
% 4.86/5.06             (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06             (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['41', '42'])).
% 4.86/5.06  thf('44', plain,
% 4.86/5.06      (![X22 : $i, X24 : $i]: ((k2_mcart_1 @ (k4_tarski @ X22 @ X24)) = (X24))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('45', plain,
% 4.86/5.06      ((((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B))
% 4.86/5.06          = (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup+', [status(thm)], ['43', '44'])).
% 4.86/5.06  thf('46', plain,
% 4.86/5.06      (![X22 : $i, X24 : $i]: ((k2_mcart_1 @ (k4_tarski @ X22 @ X24)) = (X24))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('47', plain,
% 4.86/5.06      ((((sk_B) = (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['45', '46'])).
% 4.86/5.06  thf('48', plain,
% 4.86/5.06      (((r2_hidden @ sk_B @ sk_E_2))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['40', '47'])).
% 4.86/5.06  thf('49', plain,
% 4.86/5.06      ((~ (r2_hidden @ sk_B @ sk_E_2)) <= (~ ((r2_hidden @ sk_B @ sk_E_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['23'])).
% 4.86/5.06  thf('50', plain,
% 4.86/5.06      (((r2_hidden @ sk_B @ sk_E_2)) | 
% 4.86/5.06       ~
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['48', '49'])).
% 4.86/5.06  thf('51', plain,
% 4.86/5.06      (((zip_tseitin_0 @ 
% 4.86/5.06         (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['36', '37'])).
% 4.86/5.06  thf('52', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.86/5.06         ((r2_hidden @ X0 @ X4) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('53', plain,
% 4.86/5.06      (((r2_hidden @ (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06         sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['51', '52'])).
% 4.86/5.06  thf('54', plain,
% 4.86/5.06      ((((k4_tarski @ sk_A @ sk_B)
% 4.86/5.06          = (k4_tarski @ 
% 4.86/5.06             (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1) @ 
% 4.86/5.06             (sk_F_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1))))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup-', [status(thm)], ['41', '42'])).
% 4.86/5.06  thf('55', plain,
% 4.86/5.06      (![X22 : $i, X23 : $i]: ((k1_mcart_1 @ (k4_tarski @ X22 @ X23)) = (X22))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('56', plain,
% 4.86/5.06      ((((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B))
% 4.86/5.06          = (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('sup+', [status(thm)], ['54', '55'])).
% 4.86/5.06  thf('57', plain,
% 4.86/5.06      (![X22 : $i, X23 : $i]: ((k1_mcart_1 @ (k4_tarski @ X22 @ X23)) = (X22))),
% 4.86/5.06      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.86/5.06  thf('58', plain,
% 4.86/5.06      ((((sk_A) = (sk_E_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ sk_D_1)))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['56', '57'])).
% 4.86/5.06  thf('59', plain,
% 4.86/5.06      (((r2_hidden @ sk_A @ sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('demod', [status(thm)], ['53', '58'])).
% 4.86/5.06  thf('60', plain,
% 4.86/5.06      ((~ (r2_hidden @ sk_A @ sk_D_1)) <= (~ ((r2_hidden @ sk_A @ sk_D_1)))),
% 4.86/5.06      inference('split', [status(esa)], ['23'])).
% 4.86/5.06  thf('61', plain,
% 4.86/5.06      (((r2_hidden @ sk_A @ sk_D_1)) | 
% 4.86/5.06       ~
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['59', '60'])).
% 4.86/5.06  thf('62', plain,
% 4.86/5.06      (~ ((r2_hidden @ sk_B @ sk_E_2)) | ~ ((r2_hidden @ sk_A @ sk_D_1)) | 
% 4.86/5.06       ~ ((r2_hidden @ sk_C @ sk_F_2)) | 
% 4.86/5.06       ~
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['23'])).
% 4.86/5.06  thf('63', plain,
% 4.86/5.06      (((r2_hidden @ sk_A @ sk_D_1)) | 
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['4'])).
% 4.86/5.06  thf('64', plain,
% 4.86/5.06      (((r2_hidden @ sk_A @ sk_D_1)) <= (((r2_hidden @ sk_A @ sk_D_1)))),
% 4.86/5.06      inference('split', [status(esa)], ['4'])).
% 4.86/5.06  thf('65', plain,
% 4.86/5.06      (((r2_hidden @ sk_B @ sk_E_2)) <= (((r2_hidden @ sk_B @ sk_E_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['0'])).
% 4.86/5.06  thf('66', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.86/5.06         ((zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X5)
% 4.86/5.06          | ~ (r2_hidden @ X0 @ X5)
% 4.86/5.06          | ~ (r2_hidden @ X1 @ X3)
% 4.86/5.06          | ((X2) != (k4_tarski @ X0 @ X1)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.86/5.06  thf('67', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 4.86/5.06         (~ (r2_hidden @ X1 @ X3)
% 4.86/5.06          | ~ (r2_hidden @ X0 @ X5)
% 4.86/5.06          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 4.86/5.06      inference('simplify', [status(thm)], ['66'])).
% 4.86/5.06  thf('68', plain,
% 4.86/5.06      ((![X0 : $i, X1 : $i]:
% 4.86/5.06          ((zip_tseitin_0 @ sk_B @ X1 @ (k4_tarski @ X1 @ sk_B) @ sk_E_2 @ X0)
% 4.86/5.06           | ~ (r2_hidden @ X1 @ X0)))
% 4.86/5.06         <= (((r2_hidden @ sk_B @ sk_E_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['65', '67'])).
% 4.86/5.06  thf('69', plain,
% 4.86/5.06      (((zip_tseitin_0 @ sk_B @ sk_A @ (k4_tarski @ sk_A @ sk_B) @ sk_E_2 @ 
% 4.86/5.06         sk_D_1))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & ((r2_hidden @ sk_B @ sk_E_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['64', '68'])).
% 4.86/5.06  thf('70', plain,
% 4.86/5.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 4.86/5.06         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 4.86/5.06          | (r2_hidden @ X8 @ X11)
% 4.86/5.06          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 4.86/5.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.86/5.06  thf('71', plain,
% 4.86/5.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.86/5.06         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 4.86/5.06          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 4.86/5.06      inference('simplify', [status(thm)], ['70'])).
% 4.86/5.06  thf('72', plain,
% 4.86/5.06      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & ((r2_hidden @ sk_B @ sk_E_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['69', '71'])).
% 4.86/5.06  thf('73', plain,
% 4.86/5.06      (((r2_hidden @ sk_C @ sk_F_2)) <= (((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('split', [status(esa)], ['2'])).
% 4.86/5.06  thf('74', plain,
% 4.86/5.06      (![X0 : $i, X1 : $i, X3 : $i, X5 : $i]:
% 4.86/5.06         (~ (r2_hidden @ X1 @ X3)
% 4.86/5.06          | ~ (r2_hidden @ X0 @ X5)
% 4.86/5.06          | (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ X3 @ X5))),
% 4.86/5.06      inference('simplify', [status(thm)], ['66'])).
% 4.86/5.06  thf('75', plain,
% 4.86/5.06      ((![X0 : $i, X1 : $i]:
% 4.86/5.06          ((zip_tseitin_0 @ sk_C @ X1 @ (k4_tarski @ X1 @ sk_C) @ sk_F_2 @ X0)
% 4.86/5.06           | ~ (r2_hidden @ X1 @ X0)))
% 4.86/5.06         <= (((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['73', '74'])).
% 4.86/5.06  thf('76', plain,
% 4.86/5.06      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 4.86/5.06         (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C) @ sk_F_2 @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & 
% 4.86/5.06             ((r2_hidden @ sk_B @ sk_E_2)) & 
% 4.86/5.06             ((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['72', '75'])).
% 4.86/5.06  thf('77', plain,
% 4.86/5.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.86/5.06         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 4.86/5.06           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 4.86/5.06      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.86/5.06  thf('78', plain,
% 4.86/5.06      (((zip_tseitin_0 @ sk_C @ (k4_tarski @ sk_A @ sk_B) @ 
% 4.86/5.06         (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ sk_F_2 @ 
% 4.86/5.06         (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & 
% 4.86/5.06             ((r2_hidden @ sk_B @ sk_E_2)) & 
% 4.86/5.06             ((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('demod', [status(thm)], ['76', '77'])).
% 4.86/5.06  thf('79', plain,
% 4.86/5.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.86/5.06         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 4.86/5.06          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 4.86/5.06      inference('simplify', [status(thm)], ['70'])).
% 4.86/5.06  thf('80', plain,
% 4.86/5.06      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2) @ sk_F_2)))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & 
% 4.86/5.06             ((r2_hidden @ sk_B @ sk_E_2)) & 
% 4.86/5.06             ((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('sup-', [status(thm)], ['78', '79'])).
% 4.86/5.06  thf('81', plain,
% 4.86/5.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.06         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 4.86/5.06           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 4.86/5.06      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.86/5.06  thf('82', plain,
% 4.86/5.06      (((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 4.86/5.06         <= (((r2_hidden @ sk_A @ sk_D_1)) & 
% 4.86/5.06             ((r2_hidden @ sk_B @ sk_E_2)) & 
% 4.86/5.06             ((r2_hidden @ sk_C @ sk_F_2)))),
% 4.86/5.06      inference('demod', [status(thm)], ['80', '81'])).
% 4.86/5.06  thf('83', plain,
% 4.86/5.06      ((~ (r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06           (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 4.86/5.06         <= (~
% 4.86/5.06             ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06               (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 4.86/5.06      inference('split', [status(esa)], ['23'])).
% 4.86/5.06  thf('84', plain,
% 4.86/5.06      (~ ((r2_hidden @ sk_A @ sk_D_1)) | 
% 4.86/5.06       ((r2_hidden @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.86/5.06         (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))) | 
% 4.86/5.06       ~ ((r2_hidden @ sk_C @ sk_F_2)) | ~ ((r2_hidden @ sk_B @ sk_E_2))),
% 4.86/5.06      inference('sup-', [status(thm)], ['82', '83'])).
% 4.86/5.06  thf('85', plain, ($false),
% 4.86/5.06      inference('sat_resolution*', [status(thm)],
% 4.86/5.06                ['1', '3', '25', '50', '61', '62', '63', '84'])).
% 4.86/5.06  
% 4.86/5.06  % SZS output end Refutation
% 4.86/5.06  
% 4.89/5.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
