%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0863+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7IhUftjDM

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  350 ( 873 expanded)
%              Number of equality atoms :   66 ( 152 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_45_type,type,(
    sk_E_45: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t19_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k2_tarski @ ( B @ C ) @ ( k2_tarski @ ( D @ E ) ) ) ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( ( k2_mcart_1 @ A )
            = D )
          | ( ( k2_mcart_1 @ A )
            = E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k2_tarski @ ( B @ C ) @ ( k2_tarski @ ( D @ E ) ) ) ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( ( k2_mcart_1 @ A )
              = D )
            | ( ( k2_mcart_1 @ A )
              = E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) @ ( k2_tarski @ ( sk_D_93 @ sk_E_45 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf('7',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X3850 @ X3851 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('9',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
      = sk_B_72 )
    | ( ( k1_mcart_1 @ sk_A_14 )
      = sk_C_93 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( sk_C_93 != sk_C_93 )
      | ( ( k1_mcart_1 @ sk_A_14 )
        = sk_B_72 ) )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
      = sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( sk_B_72 != sk_B_72 )
   <= ( ( ( k1_mcart_1 @ sk_A_14 )
       != sk_C_93 )
      & ( ( k1_mcart_1 @ sk_A_14 )
       != sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
      = sk_C_93 )
    | ( ( k1_mcart_1 @ sk_A_14 )
      = sk_B_72 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['12'])).

thf('20',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_B_72 @ sk_C_93 ) @ ( k2_tarski @ ( sk_D_93 @ sk_E_45 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X3850 @ X3852 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ ( k2_tarski @ ( sk_D_93 @ sk_E_45 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
      = sk_D_93 )
    | ( ( k2_mcart_1 @ sk_A_14 )
      = sk_E_45 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 ) ),
    inference(split,[status(esa)],['4'])).

thf('26',plain,
    ( ( ( sk_E_45 != sk_E_45 )
      | ( ( k2_mcart_1 @ sk_A_14 )
        = sk_D_93 ) )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
      = sk_D_93 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_E_45 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( sk_D_93 != sk_D_93 )
   <= ( ( ( k2_mcart_1 @ sk_A_14 )
       != sk_E_45 )
      & ( ( k2_mcart_1 @ sk_A_14 )
       != sk_D_93 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
      = sk_D_93 )
    | ( ( k2_mcart_1 @ sk_A_14 )
      = sk_E_45 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','18','19','30'])).

%------------------------------------------------------------------------------
