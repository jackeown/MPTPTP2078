%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0923+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3hFLOXRio6

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:43 EST 2020

% Result     : Theorem 8.91s
% Output     : Refutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 122 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  713 (1813 expanded)
%              Number of equality atoms :   23 (  63 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i > $i > $i > $i > $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X20 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

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

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) @ ( sk_E_1 @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) @ X4 @ X0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t72_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_zfmisc_1 @ B @ C @ D ) )
        & ! [E: $i,F: $i,G: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( r2_hidden @ G @ D )
              & ( A
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( X24
        = ( k3_mcart_1 @ ( sk_E_2 @ X27 @ X26 @ X25 @ X24 ) @ ( sk_F_2 @ X27 @ X26 @ X25 @ X24 ) @ ( sk_G @ X27 @ X26 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('12',plain,
    ( ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) )
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ ( sk_F_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ ( sk_G @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_mcart_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k4_tarski @ ( k3_mcart_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_mcart_1 @ ( sk_E_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ ( sk_F_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ ( sk_G @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ X0 )
      = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( r2_hidden @ ( sk_E_2 @ X27 @ X26 @ X25 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( sk_E_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( r2_hidden @ X30 @ sk_D_1 )
      | ( sk_A
       != ( k4_mcart_1 @ X28 @ X29 @ X30 @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_E_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_3 )
      | ( sk_A
       != ( k4_mcart_1 @ ( sk_E_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_G @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( r2_hidden @ ( sk_F_2 @ X27 @ X26 @ X25 @ X24 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('23',plain,(
    r2_hidden @ ( sk_F_2 @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( r2_hidden @ ( sk_G @ X27 @ X26 @ X25 @ X24 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_mcart_1])).

thf('26',plain,(
    r2_hidden @ ( sk_G @ sk_D_1 @ sk_C @ sk_B @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_3 ) ) ),
    inference(demod,[status(thm)],['20','23','26'])).

thf('28',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ sk_E_3 ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ ( sk_E_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_3 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D_1 ) ) @ sk_E_3 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).


%------------------------------------------------------------------------------
