%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kLlYvLQLIg

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:16 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 170 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          : 1012 (2246 expanded)
%              Number of equality atoms :   43 ( 116 expanded)
%              Maximal formula depth    :   23 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t72_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) )
        & ! [E: $i,F: $i,G: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( r2_hidden @ G @ D )
              & ( A
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) )
      | ( X30
        = ( k3_mcart_1 @ ( sk_E_2 @ X33 @ X32 @ X31 @ X30 ) @ ( sk_F_2 @ X33 @ X32 @ X31 @ X30 ) @ ( sk_G @ X33 @ X32 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k3_mcart_1 @ ( sk_E_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ ( sk_F_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ ( sk_G @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ ( sk_F_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ ( sk_G @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) )
      | ( r2_hidden @ ( sk_E_2 @ X33 @ X32 @ X31 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

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

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A )
    = ( k4_tarski @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_mcart_1 @ X22 @ X23 @ X24 @ X25 )
      = ( k4_tarski @ ( k3_mcart_1 @ X22 @ X23 @ X24 ) @ X25 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ X1 @ X0 )
      = ( k4_mcart_1 @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ~ ( r2_hidden @ X35 @ sk_C )
      | ~ ( r2_hidden @ X36 @ sk_D_1 )
      | ( sk_A
       != ( k4_mcart_1 @ X34 @ X35 @ X36 @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_E_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_3 )
      | ( sk_A
       != ( k4_mcart_1 @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,(
    r2_hidden @ ( sk_F_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( sk_E_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_3 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_G @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_E_3 )
    | ~ ( r2_hidden @ ( sk_F_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) )
      | ( r2_hidden @ ( sk_G @ X33 @ X32 @ X31 @ X30 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_G @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_G @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_E_3 ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) )
      | ( r2_hidden @ ( sk_F_2 @ X33 @ X32 @ X31 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_F_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F_2 @ X0 @ X1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X4 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( sk_F_2 @ sk_E_3 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['41','46','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kLlYvLQLIg
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.46/2.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.46/2.66  % Solved by: fo/fo7.sh
% 2.46/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.46/2.66  % done 620 iterations in 2.166s
% 2.46/2.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.46/2.66  % SZS output start Refutation
% 2.46/2.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.46/2.66  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.46/2.66  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.46/2.66  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i > $i).
% 2.46/2.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.46/2.66  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 2.46/2.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.46/2.66  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 2.46/2.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.46/2.66  thf(sk_F_2_type, type, sk_F_2: $i > $i > $i > $i > $i).
% 2.46/2.66  thf(sk_C_type, type, sk_C: $i).
% 2.46/2.66  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.46/2.66  thf(sk_E_3_type, type, sk_E_3: $i).
% 2.46/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.46/2.66  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 2.46/2.66  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 2.46/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.46/2.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.46/2.66  thf(t83_mcart_1, conjecture,
% 2.46/2.66    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.46/2.66     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 2.46/2.66          ( ![F:$i,G:$i,H:$i,I:$i]:
% 2.46/2.66            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 2.46/2.66                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 2.46/2.66                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 2.46/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.46/2.66    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.46/2.66        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 2.46/2.66             ( ![F:$i,G:$i,H:$i,I:$i]:
% 2.46/2.66               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 2.46/2.66                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 2.46/2.66                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 2.46/2.66    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 2.46/2.66  thf('0', plain,
% 2.46/2.66      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.66  thf(d3_zfmisc_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i]:
% 2.46/2.66     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 2.46/2.66       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 2.46/2.66  thf('1', plain,
% 2.46/2.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 2.46/2.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.66  thf('2', plain,
% 2.46/2.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 2.46/2.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.66  thf('3', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 2.46/2.66      inference('sup+', [status(thm)], ['1', '2'])).
% 2.46/2.66  thf(t53_mcart_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.46/2.66     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 2.46/2.66       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 2.46/2.66  thf('4', plain,
% 2.46/2.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.46/2.66         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 2.46/2.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28) @ 
% 2.46/2.66              X29))),
% 2.46/2.66      inference('cnf', [status(esa)], [t53_mcart_1])).
% 2.46/2.66  thf('5', plain,
% 2.46/2.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ X19 @ X20 @ X21)
% 2.46/2.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20) @ X21))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.46/2.66  thf('6', plain,
% 2.46/2.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.46/2.66         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X26 @ X27 @ X28) @ X29))),
% 2.46/2.66      inference('demod', [status(thm)], ['4', '5'])).
% 2.46/2.66  thf('7', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 2.46/2.66      inference('demod', [status(thm)], ['3', '6'])).
% 2.46/2.66  thf(t72_mcart_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.46/2.66     ( ~( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) ) & 
% 2.46/2.66          ( ![E:$i,F:$i,G:$i]:
% 2.46/2.66            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 2.46/2.66                 ( r2_hidden @ G @ D ) & ( ( A ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 2.46/2.66  thf('8', plain,
% 2.46/2.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X30 @ (k3_zfmisc_1 @ X31 @ X32 @ X33))
% 2.46/2.66          | ((X30)
% 2.46/2.66              = (k3_mcart_1 @ (sk_E_2 @ X33 @ X32 @ X31 @ X30) @ 
% 2.46/2.66                 (sk_F_2 @ X33 @ X32 @ X31 @ X30) @ 
% 2.46/2.66                 (sk_G @ X33 @ X32 @ X31 @ X30))))),
% 2.46/2.66      inference('cnf', [status(esa)], [t72_mcart_1])).
% 2.46/2.66  thf('9', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.66          | ((X4)
% 2.46/2.66              = (k3_mcart_1 @ 
% 2.46/2.66                 (sk_E_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ 
% 2.46/2.66                 (sk_F_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ 
% 2.46/2.66                 (sk_G @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4))))),
% 2.46/2.66      inference('sup-', [status(thm)], ['7', '8'])).
% 2.46/2.66  thf('10', plain,
% 2.46/2.66      (((sk_A)
% 2.46/2.66         = (k3_mcart_1 @ 
% 2.46/2.66            (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66            (sk_F_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66            (sk_G @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A)))),
% 2.46/2.66      inference('sup-', [status(thm)], ['0', '9'])).
% 2.46/2.66  thf('11', plain,
% 2.46/2.66      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.66  thf('12', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 2.46/2.66      inference('sup+', [status(thm)], ['1', '2'])).
% 2.46/2.66  thf('13', plain,
% 2.46/2.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X30 @ (k3_zfmisc_1 @ X31 @ X32 @ X33))
% 2.46/2.66          | (r2_hidden @ (sk_E_2 @ X33 @ X32 @ X31 @ X30) @ X31))),
% 2.46/2.66      inference('cnf', [status(esa)], [t72_mcart_1])).
% 2.46/2.66  thf('14', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0))
% 2.46/2.66          | (r2_hidden @ (sk_E_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ 
% 2.46/2.66             (k2_zfmisc_1 @ X3 @ X2)))),
% 2.46/2.66      inference('sup-', [status(thm)], ['12', '13'])).
% 2.46/2.66  thf('15', plain,
% 2.46/2.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.46/2.66         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X26 @ X27 @ X28) @ X29))),
% 2.46/2.66      inference('demod', [status(thm)], ['4', '5'])).
% 2.46/2.66  thf('16', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.66          | (r2_hidden @ (sk_E_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ 
% 2.46/2.66             (k2_zfmisc_1 @ X3 @ X2)))),
% 2.46/2.66      inference('demod', [status(thm)], ['14', '15'])).
% 2.46/2.66  thf('17', plain,
% 2.46/2.66      ((r2_hidden @ 
% 2.46/2.66        (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 2.46/2.66      inference('sup-', [status(thm)], ['11', '16'])).
% 2.46/2.66  thf(d2_zfmisc_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i]:
% 2.46/2.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.46/2.66       ( ![D:$i]:
% 2.46/2.66         ( ( r2_hidden @ D @ C ) <=>
% 2.46/2.66           ( ?[E:$i,F:$i]:
% 2.46/2.66             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.46/2.66               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.46/2.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.46/2.66  thf(zf_stmt_2, axiom,
% 2.46/2.66    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.46/2.66     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.46/2.66       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.46/2.66         ( r2_hidden @ E @ A ) ) ))).
% 2.46/2.66  thf(zf_stmt_3, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i]:
% 2.46/2.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.46/2.66       ( ![D:$i]:
% 2.46/2.66         ( ( r2_hidden @ D @ C ) <=>
% 2.46/2.66           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.46/2.66  thf('18', plain,
% 2.46/2.66      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X12 @ X11)
% 2.46/2.66          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 2.46/2.66             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 2.46/2.66          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.66  thf('19', plain,
% 2.46/2.66      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.46/2.66         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 2.46/2.66           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 2.46/2.66          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 2.46/2.66      inference('simplify', [status(thm)], ['18'])).
% 2.46/2.66  thf('20', plain,
% 2.46/2.66      ((zip_tseitin_0 @ 
% 2.46/2.66        (sk_F_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66        sk_C @ sk_B)),
% 2.46/2.66      inference('sup-', [status(thm)], ['17', '19'])).
% 2.46/2.66  thf('21', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (((X2) = (k4_tarski @ X0 @ X1))
% 2.46/2.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.46/2.66  thf('22', plain,
% 2.46/2.66      (((sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A)
% 2.46/2.66         = (k4_tarski @ 
% 2.46/2.66            (sk_E_1 @ 
% 2.46/2.66             (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66             sk_C @ sk_B) @ 
% 2.46/2.66            (sk_F_1 @ 
% 2.46/2.66             (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66             sk_C @ sk_B)))),
% 2.46/2.66      inference('sup-', [status(thm)], ['20', '21'])).
% 2.46/2.66  thf(d3_mcart_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i]:
% 2.46/2.66     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.46/2.66  thf('23', plain,
% 2.46/2.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 2.46/2.66           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.66  thf('24', plain,
% 2.46/2.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 2.46/2.66           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.66  thf('25', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 2.46/2.66      inference('sup+', [status(thm)], ['23', '24'])).
% 2.46/2.66  thf(t31_mcart_1, axiom,
% 2.46/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.46/2.66     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 2.46/2.66       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 2.46/2.66  thf('26', plain,
% 2.46/2.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.46/2.66         ((k4_mcart_1 @ X22 @ X23 @ X24 @ X25)
% 2.46/2.66           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24) @ X25))),
% 2.46/2.66      inference('cnf', [status(esa)], [t31_mcart_1])).
% 2.46/2.66  thf('27', plain,
% 2.46/2.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 2.46/2.66           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 2.46/2.66      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.46/2.66  thf('28', plain,
% 2.46/2.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.46/2.66         ((k4_mcart_1 @ X22 @ X23 @ X24 @ X25)
% 2.46/2.66           = (k4_tarski @ (k3_mcart_1 @ X22 @ X23 @ X24) @ X25))),
% 2.46/2.66      inference('demod', [status(thm)], ['26', '27'])).
% 2.46/2.66  thf('29', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 2.46/2.66      inference('demod', [status(thm)], ['25', '28'])).
% 2.46/2.66  thf('30', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i]:
% 2.46/2.66         ((k3_mcart_1 @ 
% 2.46/2.66           (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66           X1 @ X0)
% 2.46/2.66           = (k4_mcart_1 @ 
% 2.46/2.66              (sk_E_1 @ 
% 2.46/2.66               (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66               sk_C @ sk_B) @ 
% 2.46/2.66              (sk_F_1 @ 
% 2.46/2.66               (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66               sk_C @ sk_B) @ 
% 2.46/2.66              X1 @ X0))),
% 2.46/2.66      inference('sup+', [status(thm)], ['22', '29'])).
% 2.46/2.66  thf('31', plain,
% 2.46/2.66      ((zip_tseitin_0 @ 
% 2.46/2.66        (sk_F_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66        sk_C @ sk_B)),
% 2.46/2.66      inference('sup-', [status(thm)], ['17', '19'])).
% 2.46/2.66  thf('32', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         ((r2_hidden @ X0 @ X4) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.46/2.66  thf('33', plain,
% 2.46/2.66      ((r2_hidden @ 
% 2.46/2.66        (sk_E_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        sk_B)),
% 2.46/2.66      inference('sup-', [status(thm)], ['31', '32'])).
% 2.46/2.66  thf('34', plain,
% 2.46/2.66      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X34 @ sk_B)
% 2.46/2.66          | ~ (r2_hidden @ X35 @ sk_C)
% 2.46/2.66          | ~ (r2_hidden @ X36 @ sk_D_1)
% 2.46/2.66          | ((sk_A) != (k4_mcart_1 @ X34 @ X35 @ X36 @ X37))
% 2.46/2.66          | ~ (r2_hidden @ X37 @ sk_E_3))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.66  thf('35', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X0 @ sk_E_3)
% 2.46/2.66          | ((sk_A)
% 2.46/2.66              != (k4_mcart_1 @ 
% 2.46/2.66                  (sk_E_1 @ 
% 2.46/2.66                   (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 2.46/2.66                    sk_A) @ 
% 2.46/2.66                   sk_C @ sk_B) @ 
% 2.46/2.66                  X2 @ X1 @ X0))
% 2.46/2.66          | ~ (r2_hidden @ X1 @ sk_D_1)
% 2.46/2.66          | ~ (r2_hidden @ X2 @ sk_C))),
% 2.46/2.66      inference('sup-', [status(thm)], ['33', '34'])).
% 2.46/2.66  thf('36', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i]:
% 2.46/2.66         (((sk_A)
% 2.46/2.66            != (k3_mcart_1 @ 
% 2.46/2.66                (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66                X1 @ X0))
% 2.46/2.66          | ~ (r2_hidden @ 
% 2.46/2.66               (sk_F_1 @ 
% 2.46/2.66                (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66                sk_C @ sk_B) @ 
% 2.46/2.66               sk_C)
% 2.46/2.66          | ~ (r2_hidden @ X1 @ sk_D_1)
% 2.46/2.66          | ~ (r2_hidden @ X0 @ sk_E_3))),
% 2.46/2.66      inference('sup-', [status(thm)], ['30', '35'])).
% 2.46/2.66  thf('37', plain,
% 2.46/2.66      ((zip_tseitin_0 @ 
% 2.46/2.66        (sk_F_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66        sk_C @ sk_B)),
% 2.46/2.66      inference('sup-', [status(thm)], ['17', '19'])).
% 2.46/2.66  thf('38', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.46/2.66  thf('39', plain,
% 2.46/2.66      ((r2_hidden @ 
% 2.46/2.66        (sk_F_1 @ 
% 2.46/2.66         (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66         sk_C @ sk_B) @ 
% 2.46/2.66        sk_C)),
% 2.46/2.66      inference('sup-', [status(thm)], ['37', '38'])).
% 2.46/2.66  thf('40', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i]:
% 2.46/2.66         (((sk_A)
% 2.46/2.66            != (k3_mcart_1 @ 
% 2.46/2.66                (sk_E_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66                X1 @ X0))
% 2.46/2.66          | ~ (r2_hidden @ X1 @ sk_D_1)
% 2.46/2.66          | ~ (r2_hidden @ X0 @ sk_E_3))),
% 2.46/2.66      inference('demod', [status(thm)], ['36', '39'])).
% 2.46/2.66  thf('41', plain,
% 2.46/2.66      ((((sk_A) != (sk_A))
% 2.46/2.66        | ~ (r2_hidden @ 
% 2.46/2.66             (sk_G @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66             sk_E_3)
% 2.46/2.66        | ~ (r2_hidden @ 
% 2.46/2.66             (sk_F_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66             sk_D_1))),
% 2.46/2.66      inference('sup-', [status(thm)], ['10', '40'])).
% 2.46/2.66  thf('42', plain,
% 2.46/2.66      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.66  thf('43', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 2.46/2.66      inference('demod', [status(thm)], ['3', '6'])).
% 2.46/2.66  thf('44', plain,
% 2.46/2.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X30 @ (k3_zfmisc_1 @ X31 @ X32 @ X33))
% 2.46/2.66          | (r2_hidden @ (sk_G @ X33 @ X32 @ X31 @ X30) @ X33))),
% 2.46/2.66      inference('cnf', [status(esa)], [t72_mcart_1])).
% 2.46/2.66  thf('45', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.66          | (r2_hidden @ (sk_G @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ X0))),
% 2.46/2.66      inference('sup-', [status(thm)], ['43', '44'])).
% 2.46/2.66  thf('46', plain,
% 2.46/2.66      ((r2_hidden @ 
% 2.46/2.66        (sk_G @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ sk_E_3)),
% 2.46/2.66      inference('sup-', [status(thm)], ['42', '45'])).
% 2.46/2.66  thf('47', plain,
% 2.46/2.66      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 @ sk_E_3))),
% 2.46/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.46/2.66  thf('48', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 2.46/2.66      inference('sup+', [status(thm)], ['1', '2'])).
% 2.46/2.66  thf('49', plain,
% 2.46/2.66      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X30 @ (k3_zfmisc_1 @ X31 @ X32 @ X33))
% 2.46/2.66          | (r2_hidden @ (sk_F_2 @ X33 @ X32 @ X31 @ X30) @ X32))),
% 2.46/2.66      inference('cnf', [status(esa)], [t72_mcart_1])).
% 2.46/2.66  thf('50', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0))
% 2.46/2.66          | (r2_hidden @ (sk_F_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ X1))),
% 2.46/2.66      inference('sup-', [status(thm)], ['48', '49'])).
% 2.46/2.66  thf('51', plain,
% 2.46/2.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.46/2.66         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 2.46/2.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X26 @ X27 @ X28) @ X29))),
% 2.46/2.66      inference('demod', [status(thm)], ['4', '5'])).
% 2.46/2.66  thf('52', plain,
% 2.46/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.66         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 2.46/2.66          | (r2_hidden @ (sk_F_2 @ X0 @ X1 @ (k2_zfmisc_1 @ X3 @ X2) @ X4) @ X1))),
% 2.46/2.66      inference('demod', [status(thm)], ['50', '51'])).
% 2.46/2.66  thf('53', plain,
% 2.46/2.66      ((r2_hidden @ 
% 2.46/2.66        (sk_F_2 @ sk_E_3 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_A) @ 
% 2.46/2.66        sk_D_1)),
% 2.46/2.66      inference('sup-', [status(thm)], ['47', '52'])).
% 2.46/2.66  thf('54', plain, (((sk_A) != (sk_A))),
% 2.46/2.66      inference('demod', [status(thm)], ['41', '46', '53'])).
% 2.46/2.66  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 2.46/2.66  
% 2.46/2.66  % SZS output end Refutation
% 2.46/2.66  
% 2.46/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
