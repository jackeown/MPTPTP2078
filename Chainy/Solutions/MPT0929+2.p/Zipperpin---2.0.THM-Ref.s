%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0929+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YEWiKwXqtj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  447 ( 915 expanded)
%              Number of equality atoms :   64 ( 126 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k19_mcart_1_type,type,(
    k19_mcart_1: $i > $i )).

thf(sk_E_48_type,type,(
    sk_E_48: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_F_35_type,type,(
    sk_F_35: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k18_mcart_1_type,type,(
    k18_mcart_1: $i > $i )).

thf(k17_mcart_1_type,type,(
    k17_mcart_1: $i > $i )).

thf(k20_mcart_1_type,type,(
    k20_mcart_1: $i > $i )).

thf(sk_B_80_type,type,(
    sk_B_80: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(t89_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k20_mcart_1 @ ( k4_tarski @ ( F @ ( k4_tarski @ ( D @ E ) ) ) ) )
        = E )
      & ( ( k19_mcart_1 @ ( k4_tarski @ ( F @ ( k4_tarski @ ( D @ E ) ) ) ) )
        = D )
      & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) ) )
        = B )
      & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k20_mcart_1 @ ( k4_tarski @ ( F @ ( k4_tarski @ ( D @ E ) ) ) ) )
          = E )
        & ( ( k19_mcart_1 @ ( k4_tarski @ ( F @ ( k4_tarski @ ( D @ E ) ) ) ) )
          = D )
        & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) ) )
          = B )
        & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t89_mcart_1])).

thf('0',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 )
    | ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 )
    | ( ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_E_48 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_E_48 )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_E_48 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X4313: $i,X4314: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4313 @ X4314 ) ) )
      = X4313 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d14_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k17_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X3790: $i] :
      ( ( k17_mcart_1 @ X3790 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ X3790 ) ) ) ),
    inference(cnf,[status(esa)],[d14_mcart_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k17_mcart_1 @ ( k4_tarski @ ( X0 @ X1 ) ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) ) )
     != sk_A_14 )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4313: $i,X4314: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4313 @ X4314 ) ) )
      = X4313 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( sk_A_14 != sk_A_14 )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
    = sk_A_14 ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X4313: $i,X4314: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4313 @ X4314 ) ) )
      = X4313 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d15_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k18_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X3791: $i] :
      ( ( k18_mcart_1 @ X3791 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ X3791 ) ) ) ),
    inference(cnf,[status(esa)],[d15_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k18_mcart_1 @ ( k4_tarski @ ( X0 @ X1 ) ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) ) )
     != sk_B_80 )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4313: $i,X4315: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4313 @ X4315 ) ) )
      = X4315 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,
    ( ( sk_B_80 != sk_B_80 )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
    = sk_B_80 ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X4313: $i,X4315: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4313 @ X4315 ) ) )
      = X4315 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d16_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k19_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X3792: $i] :
      ( ( k19_mcart_1 @ X3792 )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ X3792 ) ) ) ),
    inference(cnf,[status(esa)],[d16_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k19_mcart_1 @ ( k4_tarski @ ( X1 @ X0 ) ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) )
     != sk_D_93 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4313: $i,X4314: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4313 @ X4314 ) ) )
      = X4313 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( sk_D_93 != sk_D_93 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
    = sk_D_93 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_E_48 )
    | ( ( k19_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
     != sk_D_93 )
    | ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_B_80 )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_80 ) @ sk_C_93 ) ) )
     != sk_A_14 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
 != sk_E_48 ),
    inference('sat_resolution*',[status(thm)],['9','17','25','26'])).

thf('28',plain,(
    ( k20_mcart_1 @ ( k4_tarski @ ( sk_F_35 @ ( k4_tarski @ ( sk_D_93 @ sk_E_48 ) ) ) ) )
 != sk_E_48 ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X4313: $i,X4315: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4313 @ X4315 ) ) )
      = X4315 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d17_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k20_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X3793: $i] :
      ( ( k20_mcart_1 @ X3793 )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ X3793 ) ) ) ),
    inference(cnf,[status(esa)],[d17_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k20_mcart_1 @ ( k4_tarski @ ( X1 @ X0 ) ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4313: $i,X4315: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4313 @ X4315 ) ) )
      = X4315 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,(
    sk_E_48 != sk_E_48 ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
