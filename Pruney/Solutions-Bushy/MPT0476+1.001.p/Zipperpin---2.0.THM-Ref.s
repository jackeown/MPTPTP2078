%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1pRhjZ8UU2

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
