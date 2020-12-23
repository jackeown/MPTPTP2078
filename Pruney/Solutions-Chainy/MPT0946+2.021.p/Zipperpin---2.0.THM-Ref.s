%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gUYkYOqbLc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  190 (1331 expanded)
%              Number of leaves         :   27 ( 395 expanded)
%              Depth                    :   52
%              Number of atoms          : 1830 (14949 expanded)
%              Number of equality atoms :  110 ( 854 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X23 ) )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X23 ) )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t51_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ? [B: $i] :
          ( ( v4_ordinal1 @ B )
          & ( r2_hidden @ A @ B )
          & ( v3_ordinal1 @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( r2_hidden @ X5 @ ( sk_B @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t51_ordinal1])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( r2_hidden @ X5 @ ( sk_B @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t51_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( X22
        = ( k1_wellord1 @ ( k1_wellord2 @ X21 ) @ X22 ) )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0
        = ( k1_wellord1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( X0
        = ( k1_wellord1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X5: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t51_ordinal1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0
        = ( k1_wellord1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('22',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('28',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X23: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X23 ) )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('37',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r4_wellord1 @ X12 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('41',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( r2_hidden @ X5 @ ( sk_B @ X5 ) )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t51_ordinal1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ ( k1_wellord2 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( sk_B @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('55',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','60'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X25 ) @ X24 )
        = ( k1_wellord2 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ sk_A )
        = ( k1_wellord2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( X22
        = ( k1_wellord1 @ ( k1_wellord2 @ X21 ) @ X22 ) )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_wellord1 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ ( k2_wellord1 @ X14 @ ( k1_wellord1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('71',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( X0 = sk_A )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','81'])).

thf('83',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X25 ) @ X24 )
        = ( k1_wellord2 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('93',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B_1 )
    = ( k1_wellord2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('95',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( X22
        = ( k1_wellord1 @ ( k1_wellord2 @ X21 ) @ X22 ) )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_wellord1 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ ( k2_wellord1 @ X14 @ ( k1_wellord1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('101',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','102'])).

thf('104',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','109'])).

thf('111',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','112'])).

thf('114',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( X22
        = ( k1_wellord1 @ ( k1_wellord2 @ X21 ) @ X22 ) )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('121',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_wellord1 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ ( k2_wellord1 @ X14 @ ( k1_wellord1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('126',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('128',plain,(
    ! [X23: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X23 ) )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('129',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('131',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X25 ) @ X24 )
        = ( k1_wellord2 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['128','141'])).

thf('143',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['127','144'])).

thf('146',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X25 ) @ X24 )
        = ( k1_wellord2 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('153',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('155',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('156',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('157',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('158',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['126','153','154','155','156','157'])).

thf('159',plain,(
    ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','158'])).

thf('160',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['159','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gUYkYOqbLc
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 156 iterations in 0.230s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.54/0.74  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.54/0.74  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.74  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.54/0.75  thf(t7_wellord2, axiom,
% 0.54/0.75    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X23 : $i]:
% 0.54/0.75         ((v2_wellord1 @ (k1_wellord2 @ X23)) | ~ (v3_ordinal1 @ X23))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.54/0.75  thf(t24_ordinal1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.75           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.54/0.75                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      (![X3 : $i, X4 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X3)
% 0.54/0.75          | (r2_hidden @ X4 @ X3)
% 0.54/0.75          | ((X4) = (X3))
% 0.54/0.75          | (r2_hidden @ X3 @ X4)
% 0.54/0.75          | ~ (v3_ordinal1 @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X23 : $i]:
% 0.54/0.75         ((v2_wellord1 @ (k1_wellord2 @ X23)) | ~ (v3_ordinal1 @ X23))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.54/0.75  thf(t51_ordinal1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.75       ( ?[B:$i]:
% 0.54/0.75         ( ( v4_ordinal1 @ B ) & ( r2_hidden @ A @ B ) & ( v3_ordinal1 @ B ) ) ) ))).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X5 : $i]: ((r2_hidden @ X5 @ (sk_B @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_ordinal1])).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X3 : $i, X4 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X3)
% 0.54/0.75          | (r2_hidden @ X4 @ X3)
% 0.54/0.75          | ((X4) = (X3))
% 0.54/0.75          | (r2_hidden @ X3 @ X4)
% 0.54/0.75          | ~ (v3_ordinal1 @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X5 : $i]: ((r2_hidden @ X5 @ (sk_B @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_ordinal1])).
% 0.54/0.75  thf(t10_wellord2, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.75           ( ( r2_hidden @ A @ B ) =>
% 0.54/0.75             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X21)
% 0.54/0.75          | ((X22) = (k1_wellord1 @ (k1_wellord2 @ X21) @ X22))
% 0.54/0.75          | ~ (r2_hidden @ X22 @ X21)
% 0.54/0.75          | ~ (v3_ordinal1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (k1_wellord1 @ (k1_wellord2 @ (sk_B @ X0)) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ (sk_B @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.75          | ((X0) = (k1_wellord1 @ (k1_wellord2 @ (sk_B @ X0)) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X5 : $i]: ((v3_ordinal1 @ (sk_B @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_ordinal1])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (k1_wellord1 @ (k1_wellord2 @ (sk_B @ X0)) @ X0)))),
% 0.54/0.75      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf(d1_wellord1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i,C:$i]:
% 0.54/0.75         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.54/0.75           ( ![D:$i]:
% 0.54/0.75             ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.75               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.75         (((X9) != (k1_wellord1 @ X8 @ X7))
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X10 @ X7) @ X8)
% 0.54/0.75          | ~ (r2_hidden @ X10 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X8))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X8)
% 0.54/0.75          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ X8 @ X7))
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X10 @ X7) @ X8))),
% 0.54/0.75      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ (k1_wellord2 @ (sk_B @ X0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['10', '12'])).
% 0.54/0.75  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.54/0.75  thf('14', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['16'])).
% 0.54/0.75  thf(t30_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ C ) =>
% 0.54/0.75       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.54/0.75         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.54/0.75           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.54/0.75          | (r2_hidden @ X0 @ (k3_relat_1 @ X2))
% 0.54/0.75          | ~ (v1_relat_1 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | (r2_hidden @ X1 @ (k3_relat_1 @ (k1_wellord2 @ (sk_B @ X0)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.75  thf('20', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf(d1_wellord2, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.54/0.75         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.54/0.75           ( ![C:$i,D:$i]:
% 0.54/0.75             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.54/0.75               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.54/0.75                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i]:
% 0.54/0.75         (((X17) != (k1_wellord2 @ X16))
% 0.54/0.75          | ((k3_relat_1 @ X17) = (X16))
% 0.54/0.75          | ~ (v1_relat_1 @ X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X16 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.54/0.75          | ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['21'])).
% 0.54/0.75  thf('23', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('24', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ X1 @ (sk_B @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['19', '20', '24'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['16'])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (((X17) != (k1_wellord2 @ X16))
% 0.54/0.75          | ~ (r2_hidden @ X18 @ X16)
% 0.54/0.75          | ~ (r2_hidden @ X19 @ X16)
% 0.54/0.75          | (r1_tarski @ X18 @ X19)
% 0.54/0.75          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X17)
% 0.54/0.75          | ~ (v1_relat_1 @ X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.54/0.75          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.54/0.75          | (r1_tarski @ X18 @ X19)
% 0.54/0.75          | ~ (r2_hidden @ X19 @ X16)
% 0.54/0.75          | ~ (r2_hidden @ X18 @ X16))),
% 0.54/0.75      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.75  thf('29', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.54/0.75          | (r1_tarski @ X18 @ X19)
% 0.54/0.75          | ~ (r2_hidden @ X19 @ X16)
% 0.54/0.75          | ~ (r2_hidden @ X18 @ X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X1 @ (sk_B @ X0))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | (r1_tarski @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['26', '30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['25', '31'])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['32'])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['3', '33'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X23 : $i]:
% 0.54/0.75         ((v2_wellord1 @ (k1_wellord2 @ X23)) | ~ (v3_ordinal1 @ X23))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.54/0.75  thf(t11_wellord2, conjecture,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.75           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.54/0.75             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i]:
% 0.54/0.75        ( ( v3_ordinal1 @ A ) =>
% 0.54/0.75          ( ![B:$i]:
% 0.54/0.75            ( ( v3_ordinal1 @ B ) =>
% 0.54/0.75              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.54/0.75                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(t50_wellord1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ B ) =>
% 0.54/0.75           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X12)
% 0.54/0.75          | (r4_wellord1 @ X12 @ X13)
% 0.54/0.75          | ~ (r4_wellord1 @ X13 @ X12)
% 0.54/0.75          | ~ (v1_relat_1 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.75  thf('40', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('41', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      ((r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.75  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X5 : $i]: ((r2_hidden @ X5 @ (sk_B @ X5)) | ~ (v3_ordinal1 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_ordinal1])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.54/0.75          | (r2_hidden @ X0 @ (k3_relat_1 @ X2))
% 0.54/0.75          | ~ (v1_relat_1 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | (r2_hidden @ X1 @ (k3_relat_1 @ (k1_wellord2 @ (sk_B @ X0)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('52', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | (r2_hidden @ X1 @ (sk_B @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ (sk_B @ X0)))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.54/0.75          | (r1_tarski @ X18 @ X19)
% 0.54/0.75          | ~ (r2_hidden @ X19 @ X16)
% 0.54/0.75          | ~ (r2_hidden @ X18 @ X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (r2_hidden @ X1 @ (sk_B @ X0))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | (r1_tarski @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '56'])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X0 @ (sk_B @ X0))
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['57'])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['44', '58'])).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['59'])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ((X0) = (sk_A))
% 0.54/0.75          | (r1_tarski @ sk_A @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['43', '60'])).
% 0.54/0.75  thf(t8_wellord2, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_tarski @ A @ B ) =>
% 0.54/0.75       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]:
% 0.54/0.75         (((k2_wellord1 @ (k1_wellord2 @ X25) @ X24) = (k1_wellord2 @ X24))
% 0.54/0.75          | ~ (r1_tarski @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((X0) = (sk_A))
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ sk_A) = (k1_wellord2 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['61', '62'])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X21)
% 0.54/0.75          | ((X22) = (k1_wellord1 @ (k1_wellord2 @ X21) @ X22))
% 0.54/0.75          | ~ (r2_hidden @ X22 @ X21)
% 0.54/0.75          | ~ (v3_ordinal1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['66'])).
% 0.54/0.75  thf(t57_wellord1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ( v2_wellord1 @ A ) =>
% 0.54/0.75         ( ![B:$i]:
% 0.54/0.75           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.54/0.75                ( r4_wellord1 @
% 0.54/0.75                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i]:
% 0.54/0.75         (~ (v2_wellord1 @ X14)
% 0.54/0.75          | ~ (r4_wellord1 @ X14 @ 
% 0.54/0.75               (k2_wellord1 @ X14 @ (k1_wellord1 @ X14 @ X15)))
% 0.54/0.75          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X14))
% 0.54/0.75          | ~ (v1_relat_1 @ X14))),
% 0.54/0.75      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.54/0.75             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('70', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('71', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.54/0.75             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ sk_A))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ((X0) = (sk_A))
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.54/0.75          | ~ (r2_hidden @ sk_A @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (sk_A))
% 0.54/0.75          | ~ (v3_ordinal1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['63', '72'])).
% 0.54/0.75  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ sk_A))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ((X0) = (sk_A))
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.54/0.75          | ~ (r2_hidden @ sk_A @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X0) = (sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (r2_hidden @ sk_A @ X0)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.54/0.75          | ((X0) = (sk_A))
% 0.54/0.75          | (r1_tarski @ X0 @ sk_A)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['75'])).
% 0.54/0.75  thf('77', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.54/0.75        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['42', '76'])).
% 0.54/0.75  thf('78', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (((r1_tarski @ sk_B_1 @ sk_A)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.54/0.75        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['77', '78'])).
% 0.54/0.75  thf('80', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      (((r1_tarski @ sk_B_1 @ sk_A)
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.54/0.75        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.54/0.75  thf('82', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | ~ (r2_hidden @ sk_A @ sk_B_1)
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['36', '81'])).
% 0.54/0.75  thf('83', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('84', plain,
% 0.54/0.75      ((~ (r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['82', '83'])).
% 0.54/0.75  thf('85', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A)
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['35', '84'])).
% 0.54/0.75  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('87', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      ((((sk_B_1) = (sk_A))
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A)
% 0.54/0.75        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.54/0.75  thf('89', plain, (((r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['88'])).
% 0.54/0.75  thf('90', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('91', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.54/0.75  thf('92', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]:
% 0.54/0.75         (((k2_wellord1 @ (k1_wellord2 @ X25) @ X24) = (k1_wellord2 @ X24))
% 0.54/0.75          | ~ (r1_tarski @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.54/0.75  thf('93', plain,
% 0.54/0.75      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B_1) = (k1_wellord2 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['91', '92'])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      (![X3 : $i, X4 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X3)
% 0.54/0.75          | (r2_hidden @ X4 @ X3)
% 0.54/0.75          | ((X4) = (X3))
% 0.54/0.75          | (r2_hidden @ X3 @ X4)
% 0.54/0.75          | ~ (v3_ordinal1 @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X21)
% 0.54/0.75          | ((X22) = (k1_wellord1 @ (k1_wellord2 @ X21) @ X22))
% 0.54/0.75          | ~ (r2_hidden @ X22 @ X21)
% 0.54/0.75          | ~ (v3_ordinal1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.54/0.75  thf('96', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['94', '95'])).
% 0.54/0.75  thf('97', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['96'])).
% 0.54/0.75  thf('98', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i]:
% 0.54/0.75         (~ (v2_wellord1 @ X14)
% 0.54/0.75          | ~ (r4_wellord1 @ X14 @ 
% 0.54/0.75               (k2_wellord1 @ X14 @ (k1_wellord1 @ X14 @ X15)))
% 0.54/0.75          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X14))
% 0.54/0.75          | ~ (v1_relat_1 @ X14))),
% 0.54/0.75      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.54/0.75  thf('99', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.54/0.75             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ X1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('100', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('102', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.54/0.75             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r2_hidden @ X1 @ X0)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.54/0.75  thf('103', plain,
% 0.54/0.75      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1)
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['93', '102'])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('105', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('106', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('107', plain,
% 0.54/0.75      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.54/0.75  thf('108', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('109', plain,
% 0.54/0.75      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.54/0.75  thf('110', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1)
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['2', '109'])).
% 0.54/0.75  thf('111', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('112', plain,
% 0.54/0.75      (((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['110', '111'])).
% 0.54/0.75  thf('113', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '112'])).
% 0.54/0.75  thf('114', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('115', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('116', plain,
% 0.54/0.75      (((r2_hidden @ sk_A @ sk_B_1)
% 0.54/0.75        | ((sk_B_1) = (sk_A))
% 0.54/0.75        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.54/0.75  thf('117', plain, ((((sk_B_1) = (sk_A)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['116'])).
% 0.54/0.75  thf('118', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('119', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 0.54/0.75  thf('120', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X21)
% 0.54/0.75          | ((X22) = (k1_wellord1 @ (k1_wellord2 @ X21) @ X22))
% 0.54/0.75          | ~ (r2_hidden @ X22 @ X21)
% 0.54/0.75          | ~ (v3_ordinal1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.54/0.75  thf('121', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['119', '120'])).
% 0.54/0.75  thf('122', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('123', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('124', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.54/0.75  thf('125', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i]:
% 0.54/0.75         (~ (v2_wellord1 @ X14)
% 0.54/0.75          | ~ (r4_wellord1 @ X14 @ 
% 0.54/0.75               (k2_wellord1 @ X14 @ (k1_wellord1 @ X14 @ X15)))
% 0.54/0.75          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X14))
% 0.54/0.75          | ~ (v1_relat_1 @ X14))),
% 0.54/0.75      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.54/0.75  thf('126', plain,
% 0.54/0.75      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ 
% 0.54/0.75           (k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.54/0.75        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1))
% 0.54/0.75        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B_1)))
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['124', '125'])).
% 0.54/0.75  thf('127', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.75  thf('128', plain,
% 0.54/0.75      (![X23 : $i]:
% 0.54/0.75         ((v2_wellord1 @ (k1_wellord2 @ X23)) | ~ (v3_ordinal1 @ X23))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.54/0.75  thf('129', plain,
% 0.54/0.75      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('130', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['59'])).
% 0.54/0.75  thf('131', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]:
% 0.54/0.75         (((k2_wellord1 @ (k1_wellord2 @ X25) @ X24) = (k1_wellord2 @ X24))
% 0.54/0.75          | ~ (r1_tarski @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.54/0.75  thf('132', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v3_ordinal1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ((X0) = (X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['130', '131'])).
% 0.54/0.75  thf('133', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.54/0.75             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.54/0.75  thf('134', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['132', '133'])).
% 0.54/0.75  thf('135', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.75          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.54/0.75          | ~ (v3_ordinal1 @ X1)
% 0.54/0.75          | (r1_tarski @ X1 @ X0)
% 0.54/0.75          | ((X1) = (X0))
% 0.54/0.75          | ~ (v3_ordinal1 @ X0)
% 0.54/0.75          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['134'])).
% 0.54/0.75  thf('136', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | ((sk_A) = (sk_B_1))
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1)
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['129', '135'])).
% 0.54/0.75  thf('137', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('138', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('139', plain,
% 0.54/0.75      ((((sk_A) = (sk_B_1))
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1)
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.54/0.75  thf('140', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('141', plain,
% 0.54/0.75      (((r1_tarski @ sk_A @ sk_B_1)
% 0.54/0.75        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['139', '140'])).
% 0.54/0.75  thf('142', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['128', '141'])).
% 0.54/0.75  thf('143', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('144', plain,
% 0.54/0.75      ((~ (r2_hidden @ sk_B_1 @ sk_A) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['142', '143'])).
% 0.54/0.75  thf('145', plain,
% 0.54/0.75      ((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.75        | ((sk_A) = (sk_B_1))
% 0.54/0.75        | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1)
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['127', '144'])).
% 0.54/0.75  thf('146', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('147', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('148', plain,
% 0.54/0.75      ((((sk_A) = (sk_B_1))
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1)
% 0.54/0.75        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.54/0.75  thf('149', plain, (((r1_tarski @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['148'])).
% 0.54/0.75  thf('150', plain, (((sk_A) != (sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('151', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.54/0.75  thf('152', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]:
% 0.54/0.75         (((k2_wellord1 @ (k1_wellord2 @ X25) @ X24) = (k1_wellord2 @ X24))
% 0.54/0.75          | ~ (r1_tarski @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.54/0.75  thf('153', plain,
% 0.54/0.75      (((k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['151', '152'])).
% 0.54/0.75  thf('154', plain,
% 0.54/0.75      ((r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.75  thf('155', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.54/0.75  thf('156', plain,
% 0.54/0.75      (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('157', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 0.54/0.75  thf('158', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['126', '153', '154', '155', '156', '157'])).
% 0.54/0.75  thf('159', plain, (~ (v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '158'])).
% 0.54/0.75  thf('160', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('161', plain, ($false), inference('demod', [status(thm)], ['159', '160'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
