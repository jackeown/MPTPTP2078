%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hNtXe1fORe

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:06 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   23
%              Number of atoms          :  956 (1745 expanded)
%              Number of equality atoms :   58 ( 109 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ ( sk_D @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X14
       != ( k4_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k4_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X14
       != ( k4_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ X6 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(t37_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_relat_1])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('29',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ ( sk_D @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k4_relat_1 @ X0 ) ) @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k4_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k4_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ X6 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('48',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','53'])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hNtXe1fORe
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 309 iterations in 0.248s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.70  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(dt_k4_relat_1, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.52/0.70  thf('0', plain,
% 0.52/0.70      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.70  thf(d4_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (![X2 : $i, X5 : $i]:
% 0.52/0.70         (((X5) = (k1_relat_1 @ X2))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ (sk_D @ X5 @ X2)) @ X2)
% 0.52/0.70          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.70  thf(d7_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( v1_relat_1 @ B ) =>
% 0.52/0.70           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.52/0.70             ( ![C:$i,D:$i]:
% 0.52/0.70               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.52/0.70                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X14)
% 0.52/0.70          | ((X14) != (k4_relat_1 @ X15))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X18 @ X16) @ X15)
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X14)
% 0.52/0.70          | ~ (v1_relat_1 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X15)
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k4_relat_1 @ X15))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X18 @ X16) @ X15)
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X15)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['2'])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ X1 @ (k4_relat_1 @ X0)) @ X1)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_D @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70              (sk_C @ X1 @ (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['1', '3'])).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_D @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70              (sk_C @ X1 @ (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | (r2_hidden @ (sk_C @ X1 @ (k4_relat_1 @ X0)) @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['0', '4'])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ X1 @ (k4_relat_1 @ X0)) @ X1)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_D @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70              (sk_C @ X1 @ (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.52/0.70  thf(d5_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.70         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.52/0.70          | (r2_hidden @ X8 @ X10)
% 0.52/0.70          | ((X10) != (k2_relat_1 @ X9)))),
% 0.52/0.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.70         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.52/0.70      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | (r2_hidden @ (sk_C @ X1 @ (k4_relat_1 @ X0)) @ X1)
% 0.52/0.70          | (r2_hidden @ (sk_C @ X1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['6', '8'])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70           (k2_relat_1 @ X0))
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('eq_fact', [status(thm)], ['9'])).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X11 @ X10)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.52/0.70          | ((X10) != (k2_relat_1 @ X9)))),
% 0.52/0.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      (![X9 : $i, X11 : $i]:
% 0.52/0.70         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.52/0.70          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ 
% 0.52/0.70              (sk_D_3 @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70              (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '12'])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X14)
% 0.52/0.70          | ((X14) != (k4_relat_1 @ X15))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X16 @ X17) @ X14)
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X15)
% 0.52/0.70          | ~ (v1_relat_1 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X15)
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X15)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X16 @ X17) @ (k4_relat_1 @ X15))
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X15)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['15'])).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['14', '16'])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70              (sk_D_3 @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ X0)) @ 
% 0.52/0.70             (k4_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['13', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ 
% 0.52/0.70           (k4_tarski @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70            (sk_D_3 @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ X0)) @ 
% 0.52/0.70           (k4_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.52/0.70         (((X5) = (k1_relat_1 @ X2))
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ X6) @ X2)
% 0.52/0.70          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70               (k2_relat_1 @ X0))
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70             (k2_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['22'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ (k4_relat_1 @ X0)) @ 
% 0.52/0.70           (k2_relat_1 @ X0))
% 0.52/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('eq_fact', [status(thm)], ['9'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('clc', [status(thm)], ['23', '24'])).
% 0.52/0.70  thf(t37_relat_1, conjecture,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.52/0.70         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i]:
% 0.52/0.70        ( ( v1_relat_1 @ A ) =>
% 0.52/0.70          ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.52/0.70            ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t37_relat_1])).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      ((((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.52/0.70        | ((k1_relat_1 @ sk_A) != (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      ((((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.52/0.70         <= (~ (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.52/0.70      inference('split', [status(esa)], ['26'])).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      (![X2 : $i, X5 : $i]:
% 0.52/0.70         (((X5) = (k1_relat_1 @ X2))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ (sk_D @ X5 @ X2)) @ X2)
% 0.52/0.70          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.70  thf('31', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.52/0.70             (k4_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.70         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.52/0.70      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((X1) = (k1_relat_1 @ X0))
% 0.52/0.70          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.52/0.70          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70           (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('eq_fact', [status(thm)], ['33'])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (![X9 : $i, X11 : $i]:
% 0.52/0.70         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.52/0.70          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ 
% 0.52/0.70              (sk_D_3 @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70               (k4_relat_1 @ X0)) @ 
% 0.52/0.70              (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0)) @ 
% 0.52/0.70             (k4_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X15)
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k4_relat_1 @ X15))
% 0.52/0.70          | (r2_hidden @ (k4_tarski @ X18 @ X16) @ X15)
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X15)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['2'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70              (sk_D_3 @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70               (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ 
% 0.52/0.70           (k4_tarski @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70            (sk_D_3 @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70             (k4_relat_1 @ X0))) @ 
% 0.52/0.70           X0)
% 0.52/0.70          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['38'])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | (r2_hidden @ 
% 0.52/0.70             (k4_tarski @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70              (sk_D_3 @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70               (k4_relat_1 @ X0))) @ 
% 0.52/0.70             X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['28', '39'])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ 
% 0.52/0.70           (k4_tarski @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70            (sk_D_3 @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70             (k4_relat_1 @ X0))) @ 
% 0.52/0.70           X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['40'])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.52/0.70         (((X5) = (k1_relat_1 @ X2))
% 0.52/0.70          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ X6) @ X2)
% 0.52/0.70          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70               (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70             (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (sk_C @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ X0) @ 
% 0.52/0.70           (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('eq_fact', [status(thm)], ['33'])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.52/0.70      inference('clc', [status(thm)], ['44', '45'])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      ((((k1_relat_1 @ sk_A) != (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.52/0.70         <= (~ (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.52/0.70      inference('split', [status(esa)], ['26'])).
% 0.52/0.70  thf('48', plain,
% 0.52/0.70      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.52/0.70         <= (~ (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.70  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.52/0.70         <= (~ (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.52/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.52/0.70  thf('51', plain,
% 0.52/0.70      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['50'])).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      (~ (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A)))) | 
% 0.52/0.70       ~ (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.52/0.70      inference('split', [status(esa)], ['26'])).
% 0.52/0.70  thf('53', plain,
% 0.52/0.70      (~ (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['27', '53'])).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['25', '54'])).
% 0.52/0.70  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('57', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.52/0.70  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
