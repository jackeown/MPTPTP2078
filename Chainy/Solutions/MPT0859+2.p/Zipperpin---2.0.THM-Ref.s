%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0859+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.En50LmmAyo

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  217 ( 611 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k2_tarski @ ( B @ C ) @ D ) ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k2_tarski @ ( B @ C ) @ D ) ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) @ sk_D_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X3850 @ X3851 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
      = sk_B_72 )
    | ( ( k1_mcart_1 @ sk_A_14 )
      = sk_C_93 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) @ sk_D_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X3850 @ X3852 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,(
    ( k1_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k1_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference(simpl_trail,[status(thm)],['7','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['11'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_D_93 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,(
    ( k1_mcart_1 @ sk_A_14 )
 != sk_B_72 ),
    inference('sat_resolution*',[status(thm)],['13','18'])).

thf('20',plain,(
    ( k1_mcart_1 @ sk_A_14 )
 != sk_B_72 ),
    inference(simpl_trail,[status(thm)],['17','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','16','20'])).

%------------------------------------------------------------------------------
