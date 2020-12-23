%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WaPeTDZFoK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 109 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   21
%              Number of atoms          :  971 (1293 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k4_tarski @ ( sk_C_1 @ X4 ) @ ( sk_D @ X4 ) ) )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t75_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
      <=> ( ( r2_hidden @ B @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X17 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_relat_1 @ X3 @ ( k6_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t76_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
          & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_relat_1])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X3 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('53',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['25','53'])).

thf('55',plain,(
    ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WaPeTDZFoK
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.60  % Solved by: fo/fo7.sh
% 0.19/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.60  % done 127 iterations in 0.154s
% 0.19/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.60  % SZS output start Refutation
% 0.19/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.60  thf(sk_D_type, type, sk_D: $i > $i).
% 0.19/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.60  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.19/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.60  thf(dt_k5_relat_1, axiom,
% 0.19/0.60    (![A:$i,B:$i]:
% 0.19/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.19/0.60       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.19/0.60  thf('0', plain,
% 0.19/0.60      (![X9 : $i, X10 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X9)
% 0.19/0.60          | ~ (v1_relat_1 @ X10)
% 0.19/0.60          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.60  thf(d3_tarski, axiom,
% 0.19/0.60    (![A:$i,B:$i]:
% 0.19/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.60  thf('1', plain,
% 0.19/0.60      (![X1 : $i, X3 : $i]:
% 0.19/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.60  thf(d1_relat_1, axiom,
% 0.19/0.60    (![A:$i]:
% 0.19/0.60     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.60       ( ![B:$i]:
% 0.19/0.60         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.60              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.60  thf('2', plain,
% 0.19/0.60      (![X4 : $i, X5 : $i]:
% 0.19/0.60         (((X4) = (k4_tarski @ (sk_C_1 @ X4) @ (sk_D @ X4)))
% 0.19/0.60          | ~ (r2_hidden @ X4 @ X5)
% 0.19/0.60          | ~ (v1_relat_1 @ X5))),
% 0.19/0.60      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.60  thf('3', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | ((sk_C @ X1 @ X0)
% 0.19/0.60              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60                 (sk_D @ (sk_C @ X1 @ X0)))))),
% 0.19/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.60  thf('4', plain,
% 0.19/0.60      (![X9 : $i, X10 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X9)
% 0.19/0.60          | ~ (v1_relat_1 @ X10)
% 0.19/0.60          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.60  thf('5', plain,
% 0.19/0.60      (![X1 : $i, X3 : $i]:
% 0.19/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.60  thf('6', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | ((sk_C @ X1 @ X0)
% 0.19/0.60              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60                 (sk_D @ (sk_C @ X1 @ X0)))))),
% 0.19/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.60  thf(t75_relat_1, axiom,
% 0.19/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.60     ( ( v1_relat_1 @ D ) =>
% 0.19/0.60       ( ( r2_hidden @
% 0.19/0.60           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.19/0.60         ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.19/0.60  thf('7', plain,
% 0.19/0.60      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.60         (~ (r2_hidden @ (k4_tarski @ X18 @ X16) @ 
% 0.19/0.60             (k5_relat_1 @ X19 @ (k6_relat_1 @ X17)))
% 0.19/0.60          | (r2_hidden @ (k4_tarski @ X18 @ X16) @ X19)
% 0.19/0.60          | ~ (v1_relat_1 @ X19))),
% 0.19/0.60      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.19/0.60  thf('8', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.60         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.19/0.60             (k5_relat_1 @ X3 @ (k6_relat_1 @ X2)))
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X3)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X1 @ X0))) @ 
% 0.19/0.60             X3))),
% 0.19/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.60  thf('9', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.19/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.60  thf('10', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.60          | ~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 0.19/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.60  thf('11', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.60          | ~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('sup-', [status(thm)], ['4', '10'])).
% 0.19/0.60  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.60  thf('12', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.60  thf('13', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.60  thf('14', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r2_hidden @ 
% 0.19/0.60           (k4_tarski @ 
% 0.19/0.60            (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.19/0.60            (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))) @ 
% 0.19/0.60           X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.60  thf('15', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 0.19/0.60      inference('sup+', [status(thm)], ['3', '14'])).
% 0.19/0.60  thf('16', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.19/0.60             X1))),
% 0.19/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.60  thf('17', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.60          | ~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('sup-', [status(thm)], ['0', '16'])).
% 0.19/0.60  thf('18', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.60  thf('19', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X1)
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.60  thf('20', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.19/0.60             X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X1))),
% 0.19/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.60  thf('21', plain,
% 0.19/0.60      (![X1 : $i, X3 : $i]:
% 0.19/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.60  thf('22', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0))),
% 0.19/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.60  thf('23', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.60  thf(t76_relat_1, conjecture,
% 0.19/0.60    (![A:$i,B:$i]:
% 0.19/0.60     ( ( v1_relat_1 @ B ) =>
% 0.19/0.60       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.19/0.60         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.19/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.60    (~( ![A:$i,B:$i]:
% 0.19/0.60        ( ( v1_relat_1 @ B ) =>
% 0.19/0.60          ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.19/0.60            ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )),
% 0.19/0.60    inference('cnf.neg', [status(esa)], [t76_relat_1])).
% 0.19/0.60  thf('24', plain,
% 0.19/0.60      ((~ (r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1)
% 0.19/0.60        | ~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1))),
% 0.19/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.60  thf('25', plain,
% 0.19/0.60      ((~ (r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1))
% 0.19/0.60         <= (~
% 0.19/0.60             ((r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1)))),
% 0.19/0.60      inference('split', [status(esa)], ['24'])).
% 0.19/0.60  thf('26', plain,
% 0.19/0.60      (![X9 : $i, X10 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X9)
% 0.19/0.60          | ~ (v1_relat_1 @ X10)
% 0.19/0.60          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.60  thf('27', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | ((sk_C @ X1 @ X0)
% 0.19/0.60              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60                 (sk_D @ (sk_C @ X1 @ X0)))))),
% 0.19/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.60  thf('28', plain,
% 0.19/0.60      (![X9 : $i, X10 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X9)
% 0.19/0.60          | ~ (v1_relat_1 @ X10)
% 0.19/0.60          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.60  thf('29', plain,
% 0.19/0.60      (![X1 : $i, X3 : $i]:
% 0.19/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.60  thf('30', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | ((sk_C @ X1 @ X0)
% 0.19/0.60              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60                 (sk_D @ (sk_C @ X1 @ X0)))))),
% 0.19/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.60  thf(t74_relat_1, axiom,
% 0.19/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.60     ( ( v1_relat_1 @ D ) =>
% 0.19/0.60       ( ( r2_hidden @
% 0.19/0.60           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.19/0.60         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.19/0.60  thf('31', plain,
% 0.19/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.60         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ 
% 0.19/0.60             (k5_relat_1 @ (k6_relat_1 @ X13) @ X15))
% 0.19/0.60          | (r2_hidden @ (k4_tarski @ X12 @ X14) @ X15)
% 0.19/0.60          | ~ (v1_relat_1 @ X15))),
% 0.19/0.60      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.19/0.60  thf('32', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.60         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.19/0.60             (k5_relat_1 @ (k6_relat_1 @ X3) @ X2))
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ X0 @ X1)
% 0.19/0.60          | ~ (v1_relat_1 @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X1 @ X0))) @ 
% 0.19/0.60             X2))),
% 0.19/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.60  thf('33', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.19/0.60      inference('sup-', [status(thm)], ['29', '32'])).
% 0.19/0.60  thf('34', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 0.19/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.60  thf('35', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('sup-', [status(thm)], ['28', '34'])).
% 0.19/0.60  thf('36', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.60  thf('37', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | (r2_hidden @ 
% 0.19/0.60             (k4_tarski @ 
% 0.19/0.60              (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.19/0.60              (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.60  thf('38', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r2_hidden @ 
% 0.19/0.60           (k4_tarski @ 
% 0.19/0.60            (sk_C_1 @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.19/0.60            (sk_D @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))) @ 
% 0.19/0.60           X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.60  thf('39', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 0.19/0.60      inference('sup+', [status(thm)], ['27', '38'])).
% 0.19/0.60  thf('40', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.19/0.60             X0))),
% 0.19/0.60      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.60  thf('41', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('sup-', [status(thm)], ['26', '40'])).
% 0.19/0.60  thf('42', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.19/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.60  thf('43', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.60  thf('44', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.19/0.60          | (r2_hidden @ (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.19/0.60             X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.60  thf('45', plain,
% 0.19/0.60      (![X1 : $i, X3 : $i]:
% 0.19/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.60  thf('46', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         (~ (v1_relat_1 @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.19/0.60          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.19/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.60  thf('47', plain,
% 0.19/0.60      (![X0 : $i, X1 : $i]:
% 0.19/0.60         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.19/0.60          | ~ (v1_relat_1 @ X0))),
% 0.19/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.60  thf('48', plain,
% 0.19/0.60      ((~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1))
% 0.19/0.60         <= (~
% 0.19/0.60             ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1)))),
% 0.19/0.60      inference('split', [status(esa)], ['24'])).
% 0.19/0.60  thf('49', plain,
% 0.19/0.60      ((~ (v1_relat_1 @ sk_B_1))
% 0.19/0.60         <= (~
% 0.19/0.60             ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1)))),
% 0.19/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.60  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.60  thf('51', plain,
% 0.19/0.60      (((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1))),
% 0.19/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.60  thf('52', plain,
% 0.19/0.60      (~ ((r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1)) | 
% 0.19/0.60       ~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1))),
% 0.19/0.60      inference('split', [status(esa)], ['24'])).
% 0.19/0.60  thf('53', plain,
% 0.19/0.60      (~ ((r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1))),
% 0.19/0.60      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.19/0.60  thf('54', plain,
% 0.19/0.60      (~ (r1_tarski @ (k5_relat_1 @ sk_B_1 @ (k6_relat_1 @ sk_A)) @ sk_B_1)),
% 0.19/0.60      inference('simpl_trail', [status(thm)], ['25', '53'])).
% 0.19/0.60  thf('55', plain, (~ (v1_relat_1 @ sk_B_1)),
% 0.19/0.60      inference('sup-', [status(thm)], ['23', '54'])).
% 0.19/0.60  thf('56', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.60  thf('57', plain, ($false), inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.60  
% 0.19/0.60  % SZS output end Refutation
% 0.19/0.60  
% 0.19/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
