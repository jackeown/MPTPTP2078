%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0907+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HMiUxWnoMG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 4.06s
% Output     : Refutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   45 (  92 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 ( 736 expanded)
%              Number of equality atoms :   45 ( 112 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_D_11_type,type,(
    sk_D_11: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_79_type,type,(
    sk_B_79: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_79 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ ( D @ E ) )
           != A ) ) )).

thf('1',plain,(
    ! [X1015: $i,X1016: $i,X1017: $i] :
      ( ( ( k4_tarski @ ( sk_D_11 @ X1015 @ ( sk_E_3 @ X1015 ) ) )
        = X1015 )
      | ~ ( r2_hidden @ ( X1015 @ ( k2_zfmisc_1 @ ( X1016 @ X1017 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('2',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('4',plain,(
    ! [X4230: $i,X4231: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4230 @ X4231 ) ) )
      = X4230 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( sk_D_11 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X4230: $i,X4232: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4230 @ X4232 ) ) )
      = X4232 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( sk_E_3 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) )
    | ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('12',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['2','5'])).

thf('13',plain,
    ( ( ( k4_tarski @ ( sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
      = sk_A_14 )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X4008: $i,X4009: $i,X4010: $i] :
      ( ( X4008
       != ( k1_mcart_1 @ X4008 ) )
      | ( X4008
       != ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('15',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != ( k1_mcart_1 @ ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X4230: $i,X4231: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4230 @ X4231 ) ) )
      = X4230 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != X4009 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A_14
 != ( k1_mcart_1 @ sk_A_14 ) ),
    inference('simplify_reflect-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) )
    | ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,
    ( sk_A_14
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A_14
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference(simpl_trail,[status(thm)],['10','20'])).

thf('22',plain,
    ( sk_A_14
    = ( sk_E_3 @ sk_A_14 ) ),
    inference(demod,[status(thm)],['8','21'])).

thf('23',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['2','5'])).

thf('24',plain,(
    ! [X4008: $i,X4009: $i,X4010: $i] :
      ( ( X4008
       != ( k2_mcart_1 @ X4008 ) )
      | ( X4008
       != ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('25',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != ( k2_mcart_1 @ ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X4230: $i,X4232: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4230 @ X4232 ) ) )
      = X4232 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('27',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != X4010 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A_14
 != ( sk_E_3 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','28'])).

%------------------------------------------------------------------------------
