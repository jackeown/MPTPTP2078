%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lcVkZiioYC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:59 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   22
%              Number of atoms          : 1069 (1671 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(t75_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
      <=> ( ( r2_hidden @ B @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X16 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X13 @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X16 ) ) )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t79_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_relat_1])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) ) @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) )
        = sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lcVkZiioYC
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.81  % Solved by: fo/fo7.sh
% 0.56/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.81  % done 326 iterations in 0.356s
% 0.56/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.81  % SZS output start Refutation
% 0.56/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.56/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.81  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.56/0.81  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.56/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.56/0.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.56/0.81  thf(dt_k5_relat_1, axiom,
% 0.56/0.81    (![A:$i,B:$i]:
% 0.56/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.56/0.81       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.56/0.81  thf('0', plain,
% 0.56/0.81      (![X9 : $i, X10 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X9)
% 0.56/0.81          | ~ (v1_relat_1 @ X10)
% 0.56/0.81          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.81  thf('1', plain,
% 0.56/0.81      (![X9 : $i, X10 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X9)
% 0.56/0.81          | ~ (v1_relat_1 @ X10)
% 0.56/0.81          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.81  thf(d2_relat_1, axiom,
% 0.56/0.81    (![A:$i]:
% 0.56/0.81     ( ( v1_relat_1 @ A ) =>
% 0.56/0.81       ( ![B:$i]:
% 0.56/0.81         ( ( v1_relat_1 @ B ) =>
% 0.56/0.81           ( ( ( A ) = ( B ) ) <=>
% 0.56/0.81             ( ![C:$i,D:$i]:
% 0.56/0.81               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.56/0.81                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.56/0.81  thf('2', plain,
% 0.56/0.81      (![X4 : $i, X5 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X4)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.56/0.81             X5)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.56/0.81             X4)
% 0.56/0.81          | ((X5) = (X4))
% 0.56/0.81          | ~ (v1_relat_1 @ X5))),
% 0.56/0.81      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.56/0.81  thf(t75_relat_1, axiom,
% 0.56/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.81     ( ( v1_relat_1 @ D ) =>
% 0.56/0.81       ( ( r2_hidden @
% 0.56/0.81           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.56/0.81         ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.56/0.81  thf('3', plain,
% 0.56/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.81         (~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ 
% 0.56/0.81             (k5_relat_1 @ X18 @ (k6_relat_1 @ X16)))
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ X17 @ X15) @ X18)
% 0.56/0.81          | ~ (v1_relat_1 @ X18))),
% 0.56/0.81      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.56/0.81  thf('4', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X2)
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X1))),
% 0.56/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.81  thf('5', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X2)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2)))),
% 0.56/0.81      inference('sup-', [status(thm)], ['1', '4'])).
% 0.56/0.81  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.56/0.81  thf('6', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.56/0.81  thf('7', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X2)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2)))),
% 0.56/0.81      inference('demod', [status(thm)], ['5', '6'])).
% 0.56/0.81  thf('8', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X2)
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.56/0.81             X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X1))),
% 0.56/0.81      inference('simplify', [status(thm)], ['7'])).
% 0.56/0.81  thf('9', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X0)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81              (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X0)
% 0.56/0.81          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (X0)))),
% 0.56/0.81      inference('eq_fact', [status(thm)], ['8'])).
% 0.56/0.81  thf('10', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (((k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (X0))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81              (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X0))),
% 0.56/0.81      inference('simplify', [status(thm)], ['9'])).
% 0.56/0.81  thf('11', plain,
% 0.56/0.81      (![X9 : $i, X10 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X9)
% 0.56/0.81          | ~ (v1_relat_1 @ X10)
% 0.56/0.81          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.56/0.81  thf('12', plain,
% 0.56/0.81      (![X4 : $i, X5 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X4)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.56/0.81             X5)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.56/0.81             X4)
% 0.56/0.81          | ((X5) = (X4))
% 0.56/0.81          | ~ (v1_relat_1 @ X5))),
% 0.56/0.81      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.56/0.81  thf(t20_relat_1, axiom,
% 0.56/0.81    (![A:$i,B:$i,C:$i]:
% 0.56/0.81     ( ( v1_relat_1 @ C ) =>
% 0.56/0.81       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.56/0.81         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.56/0.81           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.56/0.81  thf('13', plain,
% 0.56/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.56/0.81         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.56/0.81          | (r2_hidden @ X13 @ (k2_relat_1 @ X14))
% 0.56/0.81          | ~ (v1_relat_1 @ X14))),
% 0.56/0.81      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.56/0.81  thf('14', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X1)
% 0.56/0.81          | ((X1) = (X0))
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.56/0.81             X1)
% 0.56/0.81          | ~ (v1_relat_1 @ X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X0)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.56/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.81  thf('15', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         ((r2_hidden @ (sk_D @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X0)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.56/0.81             X1)
% 0.56/0.81          | ((X1) = (X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X1))),
% 0.56/0.81      inference('simplify', [status(thm)], ['14'])).
% 0.56/0.81  thf('16', plain,
% 0.56/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.81         (~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ 
% 0.56/0.81             (k5_relat_1 @ X18 @ (k6_relat_1 @ X16)))
% 0.56/0.81          | (r2_hidden @ X15 @ X16)
% 0.56/0.81          | ~ (v1_relat_1 @ X18))),
% 0.56/0.81      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.56/0.81  thf('17', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2))
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             (k2_relat_1 @ X2))
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             X0))),
% 0.56/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.56/0.81  thf('18', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             (k2_relat_1 @ X2))
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2)))),
% 0.56/0.81      inference('sup-', [status(thm)], ['11', '17'])).
% 0.56/0.81  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.56/0.81  thf('20', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             (k2_relat_1 @ X2))
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2)))),
% 0.56/0.81      inference('demod', [status(thm)], ['18', '19'])).
% 0.56/0.81  thf('21', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (X2))
% 0.56/0.81          | ~ (v1_relat_1 @ X2)
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             (k2_relat_1 @ X2))
% 0.56/0.81          | (r2_hidden @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X1))),
% 0.56/0.81      inference('simplify', [status(thm)], ['20'])).
% 0.56/0.81  thf(t79_relat_1, conjecture,
% 0.56/0.81    (![A:$i,B:$i]:
% 0.56/0.81     ( ( v1_relat_1 @ B ) =>
% 0.56/0.81       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.56/0.81         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.56/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.81    (~( ![A:$i,B:$i]:
% 0.56/0.81        ( ( v1_relat_1 @ B ) =>
% 0.56/0.81          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.56/0.81            ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ) )),
% 0.56/0.81    inference('cnf.neg', [status(esa)], [t79_relat_1])).
% 0.56/0.81  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf(d3_tarski, axiom,
% 0.56/0.81    (![A:$i,B:$i]:
% 0.56/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.56/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.56/0.81  thf('23', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.56/0.81          | (r2_hidden @ X0 @ X2)
% 0.56/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.56/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.81  thf('24', plain,
% 0.56/0.81      (![X0 : $i]:
% 0.56/0.81         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.56/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.56/0.81  thf('25', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (sk_D @ sk_B @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)
% 0.56/0.81          | ~ (v1_relat_1 @ sk_B)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (sk_B))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (sk_D @ sk_B @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ sk_A))),
% 0.56/0.81      inference('sup-', [status(thm)], ['21', '24'])).
% 0.56/0.81  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('27', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X1)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (sk_D @ sk_B @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)
% 0.56/0.81          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (sk_B))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (sk_D @ sk_B @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ sk_A))),
% 0.56/0.81      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.81  thf('28', plain,
% 0.56/0.81      (![X0 : $i]:
% 0.56/0.81         ((r2_hidden @ 
% 0.56/0.81           (sk_D @ sk_B @ (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A))) @ sk_A)
% 0.56/0.81          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81          | ~ (v1_relat_1 @ X0))),
% 0.56/0.81      inference('eq_fact', [status(thm)], ['27'])).
% 0.56/0.81  thf('29', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i]:
% 0.56/0.81         (((k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (X0))
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81              (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 0.56/0.81             X0)
% 0.56/0.81          | ~ (v1_relat_1 @ X0))),
% 0.56/0.81      inference('simplify', [status(thm)], ['9'])).
% 0.56/0.81  thf('30', plain,
% 0.56/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.81         (~ (r2_hidden @ X15 @ X16)
% 0.56/0.81          | ~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ X18)
% 0.56/0.81          | (r2_hidden @ (k4_tarski @ X17 @ X15) @ 
% 0.56/0.81             (k5_relat_1 @ X18 @ (k6_relat_1 @ X16)))
% 0.56/0.81          | ~ (v1_relat_1 @ X18))),
% 0.56/0.81      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.56/0.81  thf('31', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X0)
% 0.56/0.81          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X0)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81              (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 0.56/0.81             (k5_relat_1 @ X0 @ (k6_relat_1 @ X2)))
% 0.56/0.81          | ~ (r2_hidden @ 
% 0.56/0.81               (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X2))),
% 0.56/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.81  thf('32', plain,
% 0.56/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.81         (~ (r2_hidden @ (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81             X2)
% 0.56/0.81          | (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.56/0.81              (sk_D @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 0.56/0.81             (k5_relat_1 @ X0 @ (k6_relat_1 @ X2)))
% 0.56/0.81          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (X0))
% 0.56/0.81          | ~ (v1_relat_1 @ X0))),
% 0.56/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.56/0.81  thf('33', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ sk_B)
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ~ (v1_relat_1 @ sk_B)
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | (r2_hidden @ 
% 0.56/0.81           (k4_tarski @ 
% 0.56/0.81            (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81            (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81           (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))))),
% 0.56/0.81      inference('sup-', [status(thm)], ['28', '32'])).
% 0.56/0.81  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('36', plain,
% 0.56/0.81      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | (r2_hidden @ 
% 0.56/0.81           (k4_tarski @ 
% 0.56/0.81            (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81            (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81           (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))))),
% 0.56/0.81      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.56/0.81  thf('37', plain,
% 0.56/0.81      (((r2_hidden @ 
% 0.56/0.81         (k4_tarski @ 
% 0.56/0.81          (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81          (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81         (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B)))),
% 0.56/0.81      inference('simplify', [status(thm)], ['36'])).
% 0.56/0.81  thf('38', plain, (((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) != (sk_B))),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('39', plain,
% 0.56/0.81      ((r2_hidden @ 
% 0.56/0.81        (k4_tarski @ 
% 0.56/0.81         (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81         (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81        (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.56/0.81      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.56/0.81  thf('40', plain,
% 0.56/0.81      (![X4 : $i, X5 : $i]:
% 0.56/0.81         (~ (v1_relat_1 @ X4)
% 0.56/0.81          | ~ (r2_hidden @ 
% 0.56/0.81               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 0.56/0.81          | ~ (r2_hidden @ 
% 0.56/0.81               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X4)
% 0.56/0.81          | ((X5) = (X4))
% 0.56/0.81          | ~ (v1_relat_1 @ X5))),
% 0.56/0.81      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.56/0.81  thf('41', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ~ (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81              (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81             sk_B)
% 0.56/0.81        | ~ (v1_relat_1 @ sk_B))),
% 0.56/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.81  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('43', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ~ (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81              (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81             sk_B))),
% 0.56/0.81      inference('demod', [status(thm)], ['41', '42'])).
% 0.56/0.81  thf('44', plain, (((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) != (sk_B))),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('45', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 0.56/0.81        | ~ (r2_hidden @ 
% 0.56/0.81             (k4_tarski @ 
% 0.56/0.81              (sk_C_1 @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 0.56/0.81              (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))) @ 
% 0.56/0.81             sk_B))),
% 0.56/0.81      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.56/0.81  thf('46', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ sk_B)
% 0.56/0.81        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))))),
% 0.56/0.81      inference('sup-', [status(thm)], ['10', '45'])).
% 0.56/0.81  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('48', plain,
% 0.56/0.81      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))
% 0.56/0.81        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A))))),
% 0.56/0.81      inference('demod', [status(thm)], ['46', '47'])).
% 0.56/0.81  thf('49', plain, (((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) != (sk_B))),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('50', plain,
% 0.56/0.81      (~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.56/0.81      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.56/0.81  thf('51', plain,
% 0.56/0.81      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 0.56/0.81      inference('sup-', [status(thm)], ['0', '50'])).
% 0.56/0.81  thf('52', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.56/0.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.56/0.81  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.56/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.81  thf('54', plain, ($false),
% 0.56/0.81      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.56/0.81  
% 0.56/0.81  % SZS output end Refutation
% 0.56/0.81  
% 0.56/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
