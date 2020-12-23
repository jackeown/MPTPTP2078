%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0929+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z3d9gfZFFj

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  552 (1218 expanded)
%              Number of equality atoms :   85 ( 193 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k20_mcart_1_type,type,(
    k20_mcart_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k19_mcart_1_type,type,(
    k19_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k17_mcart_1_type,type,(
    k17_mcart_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k18_mcart_1_type,type,(
    k18_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = D ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15
       != ( k2_mcart_1 @ X12 ) )
      | ( X15 = X16 )
      | ( X12
       != ( k4_tarski @ X17 @ X16 ) )
      | ( X12
       != ( k4_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('1',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( ( k4_tarski @ X17 @ X16 )
       != ( k4_tarski @ X13 @ X14 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X16 ) )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['1'])).

thf(d17_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k20_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k20_mcart_1 @ X3 )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d17_mcart_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k20_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t89_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
        = E )
      & ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
        = D )
      & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
        = B )
      & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
          = E )
        & ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
          = D )
        & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
          = B )
        & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t89_mcart_1])).

thf('5',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A )
    | ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 )
    | ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_D_2 @ sk_E ) )
     != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['1'])).

thf('9',plain,
    ( ( sk_E != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( $false
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k1_mcart_1 @ X5 ) )
      | ( X8 = X9 )
      | ( X5
       != ( k4_tarski @ X9 @ X10 ) )
      | ( X5
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( ( k4_tarski @ X9 @ X10 )
       != ( k4_tarski @ X6 @ X7 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) )
        = X9 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['12'])).

thf(d15_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k18_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k18_mcart_1 @ X1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d15_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k18_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['1'])).

thf('19',plain,
    ( ( sk_B != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
    = sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['12'])).

thf(d14_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k17_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k17_mcart_1 @ X0 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d14_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k17_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('27',plain,
    ( ( sk_A != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
    = sk_A ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['1'])).

thf(d16_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k19_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k19_mcart_1 @ X2 )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d16_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k19_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_D_2 @ sk_E ) )
     != sk_D_2 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('35',plain,
    ( ( sk_D_2 != sk_D_2 )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
    = sk_D_2 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_E )
    | ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
     != sk_D_2 )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_A )
    | ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ) )
     != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('38',plain,(
    ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D_2 @ sk_E ) ) )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['20','28','36','37'])).

thf('39',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['10','38'])).


%------------------------------------------------------------------------------
