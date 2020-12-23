%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adlNms2ePQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:56 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 236 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   20
%              Number of atoms          :  964 (2715 expanded)
%              Number of equality atoms :   86 ( 223 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t71_relat_1,conjecture,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
          = A )
        & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t71_relat_1])).

thf('0',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A )
    | ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A )
   <= ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X7 ) @ ( sk_D_1 @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('10',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X7 ) @ X11 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_A != sk_A )
   <= ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = sk_A ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A )
    | ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X17 @ X14 ) @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_3 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_3 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( sk_C_2 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_3 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X17 @ X14 ) @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ X1 ) @ ( sk_C_2 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X17 @ X14 ) @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_3 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','65'])).

thf('67',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['24','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adlNms2ePQ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 176 iterations in 0.166s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.43/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.43/0.62  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(t71_relat_1, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.62          ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t71_relat_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) != (sk_A))
% 0.43/0.62        | ((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) != (sk_A)))
% 0.43/0.62         <= (~ (((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf(d4_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X7 : $i, X10 : $i]:
% 0.43/0.62         (((X10) = (k1_relat_1 @ X7))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_C_1 @ X10 @ X7) @ (sk_D_1 @ X10 @ X7)) @ X7)
% 0.43/0.62          | (r2_hidden @ (sk_C_1 @ X10 @ X7) @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.62  thf(d10_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.43/0.62         ( ![C:$i,D:$i]:
% 0.43/0.62           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.43/0.62             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((X0) != (k6_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ X2 @ X1)
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ X2 @ X1))),
% 0.43/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.43/0.62  thf('5', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ X2 @ X1))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 0.43/0.62          | ((X1) = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_1 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('eq_fact', [status(thm)], ['7'])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.62         (((X0) != (k6_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.43/0.62          | ((X2) != (X4))
% 0.43/0.62          | ~ (r2_hidden @ X2 @ X1)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X1 : $i, X4 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.62          | ~ (r2_hidden @ X4 @ X1)
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.62  thf('11', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X1 : $i, X4 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X1)
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_C_1 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62              (sk_C_1 @ X0 @ (k6_relat_1 @ X0))) @ 
% 0.43/0.62             (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '12'])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X7 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (((X10) = (k1_relat_1 @ X7))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X10 @ X7) @ X11) @ X7)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X7) @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_1 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('eq_fact', [status(thm)], ['7'])).
% 0.43/0.62  thf('18', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (sk_A)))
% 0.43/0.62         <= (~ (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      ((((sk_A) != (sk_A)))
% 0.43/0.62         <= (~ (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('21', plain, ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (~ (((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))) | 
% 0.43/0.62       ~ (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('23', plain, (~ (((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain, (((k2_relat_1 @ (k6_relat_1 @ sk_A)) != (sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.43/0.62  thf(d5_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_D_3 @ X17 @ X14) @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((X0) != (k6_relat_1 @ X1))
% 0.43/0.62          | ((X2) = (X3))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.43/0.62          | ((X2) = (X3)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.43/0.62  thf('28', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.43/0.62          | ((X2) = (X3)))),
% 0.43/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 0.43/0.62          | ((X1) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((sk_D_3 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (![X1 : $i, X4 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X1)
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((sk_D_3 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.62            = (sk_C_2 @ X0 @ (k6_relat_1 @ X1)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X1)))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_C_2 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.43/0.62              (sk_C_2 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.43/0.62             (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X18 @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((sk_D_3 @ X0 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X0 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((sk_D_3 @ X0 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X0 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 0.43/0.62          | ((X1) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((sk_D_3 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '29'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((sk_D_3 @ X0 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X0 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('clc', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_D_3 @ X17 @ X14) @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.43/0.62          | (r2_hidden @ X5 @ X8)
% 0.43/0.62          | ((X8) != (k1_relat_1 @ X7)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.62         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.43/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.43/0.62          | ((X1) = (k2_relat_1 @ X0))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['38', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X1 : $i, X4 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X1)
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_D_3 @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_C_2 @ X0 @ X1) @ (sk_C_2 @ X0 @ X1)) @ 
% 0.43/0.62             (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X18 @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf('46', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_D_3 @ X17 @ X14) @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.43/0.62          | (r2_hidden @ X2 @ X1))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 0.43/0.62          | ((X1) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('clc', [status(thm)], ['48', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X1 : $i, X4 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X1)
% 0.43/0.62          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62              (sk_D_3 @ X0 @ (k6_relat_1 @ X0))) @ 
% 0.43/0.62             (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ 
% 0.43/0.62           (k4_tarski @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62            (sk_C_2 @ X0 @ (k6_relat_1 @ X0))) @ 
% 0.43/0.62           (k6_relat_1 @ X0))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['37', '54'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k4_tarski @ (sk_D_3 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62              (sk_C_2 @ X0 @ (k6_relat_1 @ X0))) @ 
% 0.43/0.62             (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         (((X17) = (k2_relat_1 @ X14))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X18 @ (sk_C_2 @ X17 @ X14)) @ X14)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X14) @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((sk_D_3 @ X0 @ (k6_relat_1 @ X0))
% 0.43/0.62              = (sk_C_2 @ X0 @ (k6_relat_1 @ X0))))),
% 0.43/0.62      inference('clc', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.43/0.62          | ((X1) = (k2_relat_1 @ X0))
% 0.43/0.62          | (r2_hidden @ (sk_D_3 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['38', '40'])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.62           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['60', '61'])).
% 0.43/0.62  thf('63', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0)
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.43/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.43/0.62  thf('66', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['59', '65'])).
% 0.43/0.62  thf('67', plain, (((sk_A) != (sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '66'])).
% 0.43/0.62  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
