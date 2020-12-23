%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P2iWtlwKWS

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:58 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   22
%              Number of atoms          : 1069 (1671 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :   18 (   9 average)

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

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
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
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
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
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X18 ) )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t77_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
         => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_relat_1])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
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
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
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
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P2iWtlwKWS
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:04:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 326 iterations in 0.400s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.66/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.85  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.66/0.85  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.66/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.85  thf(dt_k5_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.66/0.85       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.66/0.85  thf('0', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X9)
% 0.66/0.85          | ~ (v1_relat_1 @ X10)
% 0.66/0.85          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X9)
% 0.66/0.85          | ~ (v1_relat_1 @ X10)
% 0.66/0.85          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.66/0.85  thf(d2_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( v1_relat_1 @ B ) =>
% 0.66/0.85           ( ( ( A ) = ( B ) ) <=>
% 0.66/0.85             ( ![C:$i,D:$i]:
% 0.66/0.85               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.66/0.85                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.66/0.85  thf('2', plain,
% 0.66/0.85      (![X4 : $i, X5 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X4)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.66/0.85             X5)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.66/0.85             X4)
% 0.66/0.85          | ((X5) = (X4))
% 0.66/0.85          | ~ (v1_relat_1 @ X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.66/0.85  thf(t74_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ D ) =>
% 0.66/0.85       ( ( r2_hidden @
% 0.66/0.85           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.66/0.85         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.66/0.85  thf('3', plain,
% 0.66/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ 
% 0.66/0.85             (k5_relat_1 @ (k6_relat_1 @ X16) @ X18))
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X18)
% 0.66/0.85          | ~ (v1_relat_1 @ X18))),
% 0.66/0.85      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X2)
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.85  thf('5', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X2)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['1', '4'])).
% 0.66/0.85  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.66/0.85  thf('6', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.85  thf('7', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X2)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2)))),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('8', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X2)
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['7'])).
% 0.66/0.85  thf('9', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X0)))),
% 0.66/0.85      inference('eq_fact', [status(thm)], ['8'])).
% 0.66/0.85  thf('10', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X0))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X9)
% 0.66/0.85          | ~ (v1_relat_1 @ X10)
% 0.66/0.85          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.66/0.85  thf('12', plain,
% 0.66/0.85      (![X4 : $i, X5 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X4)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.66/0.85             X5)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.66/0.85             X4)
% 0.66/0.85          | ((X5) = (X4))
% 0.66/0.85          | ~ (v1_relat_1 @ X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.66/0.85  thf(t20_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ C ) =>
% 0.66/0.85       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.66/0.85         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.66/0.85           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.66/0.85  thf('13', plain,
% 0.66/0.85      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.85         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.66/0.85          | (r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 0.66/0.85          | ~ (v1_relat_1 @ X14))),
% 0.66/0.85      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.66/0.85  thf('14', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X1)
% 0.66/0.85          | ((X1) = (X0))
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.66/0.85             X1)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['12', '13'])).
% 0.66/0.85  thf('15', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.66/0.85             X1)
% 0.66/0.85          | ((X1) = (X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X1))),
% 0.66/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.66/0.85  thf('16', plain,
% 0.66/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ 
% 0.66/0.85             (k5_relat_1 @ (k6_relat_1 @ X16) @ X18))
% 0.66/0.85          | (r2_hidden @ X15 @ X16)
% 0.66/0.85          | ~ (v1_relat_1 @ X18))),
% 0.66/0.85      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2))
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85             (k1_relat_1 @ X2))
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1))),
% 0.66/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.85  thf('18', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85             (k1_relat_1 @ X2))
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['11', '17'])).
% 0.66/0.85  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.85  thf('20', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1)
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85             (k1_relat_1 @ X2))
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2)))),
% 0.66/0.85      inference('demod', [status(thm)], ['18', '19'])).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X2))
% 0.66/0.85          | ~ (v1_relat_1 @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85             (k1_relat_1 @ X2))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.66/0.85  thf(t77_relat_1, conjecture,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ B ) =>
% 0.66/0.85       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.66/0.85         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i,B:$i]:
% 0.66/0.85        ( ( v1_relat_1 @ B ) =>
% 0.66/0.85          ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.66/0.85            ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t77_relat_1])).
% 0.66/0.85  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(d3_tarski, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.85  thf('23', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X0 @ X1)
% 0.66/0.85          | (r2_hidden @ X0 @ X2)
% 0.66/0.85          | ~ (r1_tarski @ X1 @ X2))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf('24', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['22', '23'])).
% 0.66/0.85  thf('25', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1)
% 0.66/0.85          | ~ (v1_relat_1 @ sk_B)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (sk_B))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['21', '24'])).
% 0.66/0.85  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('27', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X1)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (sk_B))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['25', '26'])).
% 0.66/0.85  thf('28', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ 
% 0.66/0.85           (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_A)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0) = (sk_B))
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('eq_fact', [status(thm)], ['27'])).
% 0.66/0.85  thf('29', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X0))
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.66/0.85  thf('30', plain,
% 0.66/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X15 @ X16)
% 0.66/0.85          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X18)
% 0.66/0.85          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ 
% 0.66/0.85             (k5_relat_1 @ (k6_relat_1 @ X16) @ X18))
% 0.66/0.85          | ~ (v1_relat_1 @ X18))),
% 0.66/0.85      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.66/0.85  thf('31', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.66/0.85          | ~ (r2_hidden @ 
% 0.66/0.85               (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X2))),
% 0.66/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.85  thf('32', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (~ (r2_hidden @ 
% 0.66/0.85             (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X2)
% 0.66/0.85          | (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.66/0.85              (sk_D @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.85             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.66/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ X0) = (X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('simplify', [status(thm)], ['31'])).
% 0.66/0.85  thf('33', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ sk_B)
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_B)
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | (r2_hidden @ 
% 0.66/0.85           (k4_tarski @ 
% 0.66/0.85            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['28', '32'])).
% 0.66/0.85  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('36', plain,
% 0.66/0.85      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | (r2_hidden @ 
% 0.66/0.85           (k4_tarski @ 
% 0.66/0.85            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.66/0.85  thf('37', plain,
% 0.66/0.85      (((r2_hidden @ 
% 0.66/0.85         (k4_tarski @ 
% 0.66/0.85          (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85          (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85         (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 0.66/0.85      inference('simplify', [status(thm)], ['36'])).
% 0.66/0.85  thf('38', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('39', plain,
% 0.66/0.85      ((r2_hidden @ 
% 0.66/0.85        (k4_tarski @ 
% 0.66/0.85         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85         (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.66/0.85  thf('40', plain,
% 0.66/0.85      (![X4 : $i, X5 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X4)
% 0.66/0.85          | ~ (r2_hidden @ 
% 0.66/0.85               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 0.66/0.85          | ~ (r2_hidden @ 
% 0.66/0.85               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X4)
% 0.66/0.85          | ((X5) = (X4))
% 0.66/0.85          | ~ (v1_relat_1 @ X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.66/0.85  thf('41', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ~ (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85             sk_B)
% 0.66/0.85        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.85  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('43', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ~ (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85             sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['41', '42'])).
% 0.66/0.85  thf('44', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('45', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.66/0.85        | ~ (r2_hidden @ 
% 0.66/0.85             (k4_tarski @ 
% 0.66/0.85              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 0.66/0.85              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 0.66/0.85             sk_B))),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.66/0.85  thf('46', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ sk_B)
% 0.66/0.85        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['10', '45'])).
% 0.66/0.85  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('48', plain,
% 0.66/0.85      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 0.66/0.85        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['46', '47'])).
% 0.66/0.85  thf('49', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('50', plain,
% 0.66/0.85      (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.66/0.85  thf('51', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['0', '50'])).
% 0.66/0.85  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('53', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.85  thf('54', plain, ($false),
% 0.66/0.85      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.66/0.85  
% 0.66/0.85  % SZS output end Refutation
% 0.66/0.85  
% 0.66/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
