%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0857+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WwsFb5sEG1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 4.96s
% Output     : Refutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  276 ( 649 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_11_type,type,(
    sk_D_11: $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ ( k1_tarski @ C ) ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ ( k1_tarski @ C ) ) ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ ( k1_tarski @ sk_C_93 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ ( k1_tarski @ sk_C_93 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ ( D @ E ) )
           != A ) ) )).

thf('2',plain,(
    ! [X1015: $i,X1016: $i,X1017: $i] :
      ( ( ( k4_tarski @ ( sk_D_11 @ X1015 @ ( sk_E_3 @ X1015 ) ) )
        = X1015 )
      | ~ ( r2_hidden @ ( X1015 @ ( k2_zfmisc_1 @ ( X1016 @ X1017 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('3',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('5',plain,(
    ! [X3882: $i,X3883: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3882 @ X3883 ) ) )
      = X3882 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( sk_D_11 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['3','6'])).

thf('9',plain,(
    ! [X3882: $i,X3884: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3882 @ X3884 ) ) )
      = X3884 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( sk_E_3 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['7','10'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ ( k2_zfmisc_1 @ ( C @ D ) ) ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ D ) ) ) ) )).

thf('12',plain,(
    ! [X1062: $i,X1063: $i,X1064: $i,X1065: $i] :
      ( ( r2_hidden @ ( X1064 @ X1065 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X1062 @ X1064 ) @ ( k2_zfmisc_1 @ ( X1063 @ X1065 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ ( k1_tarski @ sk_C_93 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = sk_C_93 ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ ( k1_tarski @ sk_C_93 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf('21',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X3850 @ X3851 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('26',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference(simpl_trail,[status(thm)],['19','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','27'])).

%------------------------------------------------------------------------------
