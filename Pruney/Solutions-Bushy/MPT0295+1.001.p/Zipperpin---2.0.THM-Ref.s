%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0295+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u5cY5rdmYn

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  71 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 729 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t103_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ D @ A )
          & ! [E: $i,F: $i] :
              ~ ( ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C )
                & ( D
                  = ( k4_tarski @ E @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,
    ( sk_D_1
    = ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_B )
      | ( sk_D_1
       != ( k4_tarski @ X20 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( sk_D_1
       != ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_D_1 != sk_D_1 ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).


%------------------------------------------------------------------------------
