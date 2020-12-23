%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ploCdAFrB7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:22 EST 2020

% Result     : Theorem 5.61s
% Output     : Refutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   71 (  86 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   17
%              Number of atoms          :  872 (1057 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k10_relat_1 @ X20 @ ( k10_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ X0 ) @ ( sk_C @ X3 @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D @ X15 @ X13 @ X14 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X15 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k10_relat_1 @ X20 @ ( k10_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t182_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t182_relat_1])).

thf('44',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ploCdAFrB7
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.61/5.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.61/5.86  % Solved by: fo/fo7.sh
% 5.61/5.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.61/5.86  % done 3338 iterations in 5.409s
% 5.61/5.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.61/5.86  % SZS output start Refutation
% 5.61/5.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.61/5.86  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.61/5.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.61/5.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.61/5.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.61/5.86  thf(sk_B_type, type, sk_B: $i).
% 5.61/5.86  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.61/5.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.61/5.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.61/5.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.61/5.86  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.61/5.86  thf(sk_A_type, type, sk_A: $i).
% 5.61/5.86  thf(dt_k5_relat_1, axiom,
% 5.61/5.86    (![A:$i,B:$i]:
% 5.61/5.86     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 5.61/5.86       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 5.61/5.86  thf('0', plain,
% 5.61/5.86      (![X10 : $i, X11 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X10)
% 5.61/5.86          | ~ (v1_relat_1 @ X11)
% 5.61/5.86          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 5.61/5.86      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 5.61/5.86  thf(t181_relat_1, axiom,
% 5.61/5.86    (![A:$i,B:$i]:
% 5.61/5.86     ( ( v1_relat_1 @ B ) =>
% 5.61/5.86       ( ![C:$i]:
% 5.61/5.86         ( ( v1_relat_1 @ C ) =>
% 5.61/5.86           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 5.61/5.86             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 5.61/5.86  thf('1', plain,
% 5.61/5.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X19)
% 5.61/5.86          | ((k10_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 5.61/5.86              = (k10_relat_1 @ X20 @ (k10_relat_1 @ X19 @ X21)))
% 5.61/5.86          | ~ (v1_relat_1 @ X20))),
% 5.61/5.86      inference('cnf', [status(esa)], [t181_relat_1])).
% 5.61/5.86  thf(t169_relat_1, axiom,
% 5.61/5.86    (![A:$i]:
% 5.61/5.86     ( ( v1_relat_1 @ A ) =>
% 5.61/5.86       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 5.61/5.86  thf('2', plain,
% 5.61/5.86      (![X18 : $i]:
% 5.61/5.86         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 5.61/5.86          | ~ (v1_relat_1 @ X18))),
% 5.61/5.86      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.61/5.86  thf('3', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (((k10_relat_1 @ X1 @ 
% 5.61/5.86            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 5.61/5.86            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 5.61/5.86      inference('sup+', [status(thm)], ['1', '2'])).
% 5.61/5.86  thf('4', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ((k10_relat_1 @ X1 @ 
% 5.61/5.86              (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 5.61/5.86              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.61/5.86      inference('sup-', [status(thm)], ['0', '3'])).
% 5.61/5.86  thf('5', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (((k10_relat_1 @ X1 @ 
% 5.61/5.86            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 5.61/5.86            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['4'])).
% 5.61/5.86  thf(d3_tarski, axiom,
% 5.61/5.86    (![A:$i,B:$i]:
% 5.61/5.86     ( ( r1_tarski @ A @ B ) <=>
% 5.61/5.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.61/5.86  thf('6', plain,
% 5.61/5.86      (![X1 : $i, X3 : $i]:
% 5.61/5.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.61/5.86      inference('cnf', [status(esa)], [d3_tarski])).
% 5.61/5.86  thf(t166_relat_1, axiom,
% 5.61/5.86    (![A:$i,B:$i,C:$i]:
% 5.61/5.86     ( ( v1_relat_1 @ C ) =>
% 5.61/5.86       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 5.61/5.86         ( ?[D:$i]:
% 5.61/5.86           ( ( r2_hidden @ D @ B ) & 
% 5.61/5.86             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 5.61/5.86             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 5.61/5.86  thf('7', plain,
% 5.61/5.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.86         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 5.61/5.86          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 5.61/5.86          | ~ (v1_relat_1 @ X15))),
% 5.61/5.86      inference('cnf', [status(esa)], [t166_relat_1])).
% 5.61/5.86  thf('8', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r2_hidden @ 
% 5.61/5.86             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 5.61/5.86      inference('sup-', [status(thm)], ['6', '7'])).
% 5.61/5.86  thf(t167_relat_1, axiom,
% 5.61/5.86    (![A:$i,B:$i]:
% 5.61/5.86     ( ( v1_relat_1 @ B ) =>
% 5.61/5.86       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 5.61/5.86  thf('9', plain,
% 5.61/5.86      (![X16 : $i, X17 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X16 @ X17) @ (k1_relat_1 @ X16))
% 5.61/5.86          | ~ (v1_relat_1 @ X16))),
% 5.61/5.86      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.61/5.86  thf('10', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         (~ (r2_hidden @ X0 @ X1)
% 5.61/5.86          | (r2_hidden @ X0 @ X2)
% 5.61/5.86          | ~ (r1_tarski @ X1 @ X2))),
% 5.61/5.86      inference('cnf', [status(esa)], [d3_tarski])).
% 5.61/5.86  thf('11', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 5.61/5.86          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ X1)))),
% 5.61/5.86      inference('sup-', [status(thm)], ['9', '10'])).
% 5.61/5.86  thf('12', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X2)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X3)
% 5.61/5.86          | (r2_hidden @ 
% 5.61/5.86             (sk_D @ X2 @ (k10_relat_1 @ X1 @ X0) @ 
% 5.61/5.86              (sk_C @ X3 @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 5.61/5.86             (k1_relat_1 @ X1))
% 5.61/5.86          | ~ (v1_relat_1 @ X1))),
% 5.61/5.86      inference('sup-', [status(thm)], ['8', '11'])).
% 5.61/5.86  thf('13', plain,
% 5.61/5.86      (![X1 : $i, X3 : $i]:
% 5.61/5.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.61/5.86      inference('cnf', [status(esa)], [d3_tarski])).
% 5.61/5.86  thf('14', plain,
% 5.61/5.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.86         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 5.61/5.86          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k2_relat_1 @ X15))
% 5.61/5.86          | ~ (v1_relat_1 @ X15))),
% 5.61/5.86      inference('cnf', [status(esa)], [t166_relat_1])).
% 5.61/5.86  thf('15', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r2_hidden @ 
% 5.61/5.86             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 5.61/5.86             (k2_relat_1 @ X1)))),
% 5.61/5.86      inference('sup-', [status(thm)], ['13', '14'])).
% 5.61/5.86  thf('16', plain,
% 5.61/5.86      (![X1 : $i, X3 : $i]:
% 5.61/5.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.61/5.86      inference('cnf', [status(esa)], [d3_tarski])).
% 5.61/5.86  thf('17', plain,
% 5.61/5.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.86         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 5.61/5.86          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D @ X15 @ X13 @ X14)) @ X15)
% 5.61/5.86          | ~ (v1_relat_1 @ X15))),
% 5.61/5.86      inference('cnf', [status(esa)], [t166_relat_1])).
% 5.61/5.86  thf('18', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r2_hidden @ 
% 5.61/5.86             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.61/5.86              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 5.61/5.86             X1))),
% 5.61/5.86      inference('sup-', [status(thm)], ['16', '17'])).
% 5.61/5.86  thf('19', plain,
% 5.61/5.86      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.86         (~ (r2_hidden @ X12 @ X13)
% 5.61/5.86          | ~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X15)
% 5.61/5.86          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X15))
% 5.61/5.86          | (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 5.61/5.86          | ~ (v1_relat_1 @ X15))),
% 5.61/5.86      inference('cnf', [status(esa)], [t166_relat_1])).
% 5.61/5.86  thf('20', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 5.61/5.86             (k10_relat_1 @ X0 @ X3))
% 5.61/5.86          | ~ (r2_hidden @ 
% 5.61/5.86               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ 
% 5.61/5.86               (k2_relat_1 @ X0))
% 5.61/5.86          | ~ (r2_hidden @ 
% 5.61/5.86               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ X3))),
% 5.61/5.86      inference('sup-', [status(thm)], ['18', '19'])).
% 5.61/5.86  thf('21', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (r2_hidden @ 
% 5.61/5.86             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ X3)
% 5.61/5.86          | ~ (r2_hidden @ 
% 5.61/5.86               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ 
% 5.61/5.86               (k2_relat_1 @ X0))
% 5.61/5.86          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 5.61/5.86             (k10_relat_1 @ X0 @ X3))
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['20'])).
% 5.61/5.86  thf('22', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 5.61/5.86          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 5.61/5.86             (k10_relat_1 @ X0 @ X3))
% 5.61/5.86          | ~ (r2_hidden @ 
% 5.61/5.86               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ X3))),
% 5.61/5.86      inference('sup-', [status(thm)], ['15', '21'])).
% 5.61/5.86  thf('23', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (r2_hidden @ 
% 5.61/5.86             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1))) @ X3)
% 5.61/5.86          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 5.61/5.86             (k10_relat_1 @ X0 @ X3))
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['22'])).
% 5.61/5.86  thf('24', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1)) @ X3)
% 5.61/5.86          | ~ (v1_relat_1 @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X2)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1)) @ X3)
% 5.61/5.86          | (r2_hidden @ 
% 5.61/5.86             (sk_C @ X3 @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1))) @ 
% 5.61/5.86             (k10_relat_1 @ X2 @ (k1_relat_1 @ X0))))),
% 5.61/5.86      inference('sup-', [status(thm)], ['12', '23'])).
% 5.61/5.86  thf('25', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.86         ((r2_hidden @ 
% 5.61/5.86           (sk_C @ X3 @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1))) @ 
% 5.61/5.86           (k10_relat_1 @ X2 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X2)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1)) @ X3)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['24'])).
% 5.61/5.86  thf('26', plain,
% 5.61/5.86      (![X1 : $i, X3 : $i]:
% 5.61/5.86         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.61/5.86      inference('cnf', [status(esa)], [d3_tarski])).
% 5.61/5.86  thf('27', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 5.61/5.86             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 5.61/5.86             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 5.61/5.86      inference('sup-', [status(thm)], ['25', '26'])).
% 5.61/5.86  thf('28', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 5.61/5.86             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['27'])).
% 5.61/5.86  thf('29', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 5.61/5.86           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1))),
% 5.61/5.86      inference('sup+', [status(thm)], ['5', '28'])).
% 5.61/5.86  thf('30', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 5.61/5.86             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 5.61/5.86      inference('simplify', [status(thm)], ['29'])).
% 5.61/5.86  thf('31', plain,
% 5.61/5.86      (![X18 : $i]:
% 5.61/5.86         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 5.61/5.86          | ~ (v1_relat_1 @ X18))),
% 5.61/5.86      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.61/5.86  thf('32', plain,
% 5.61/5.86      (![X10 : $i, X11 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X10)
% 5.61/5.86          | ~ (v1_relat_1 @ X11)
% 5.61/5.86          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 5.61/5.86      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 5.61/5.86  thf('33', plain,
% 5.61/5.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X19)
% 5.61/5.86          | ((k10_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 5.61/5.86              = (k10_relat_1 @ X20 @ (k10_relat_1 @ X19 @ X21)))
% 5.61/5.86          | ~ (v1_relat_1 @ X20))),
% 5.61/5.86      inference('cnf', [status(esa)], [t181_relat_1])).
% 5.61/5.86  thf('34', plain,
% 5.61/5.86      (![X16 : $i, X17 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X16 @ X17) @ (k1_relat_1 @ X16))
% 5.61/5.86          | ~ (v1_relat_1 @ X16))),
% 5.61/5.86      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.61/5.86  thf('35', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.61/5.86           (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 5.61/5.86          | ~ (v1_relat_1 @ X2)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 5.61/5.86      inference('sup+', [status(thm)], ['33', '34'])).
% 5.61/5.86  thf('36', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 5.61/5.86             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.61/5.86      inference('sup-', [status(thm)], ['32', '35'])).
% 5.61/5.86  thf('37', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 5.61/5.86           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['36'])).
% 5.61/5.86  thf('38', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.61/5.86           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1))),
% 5.61/5.86      inference('sup+', [status(thm)], ['31', '37'])).
% 5.61/5.86  thf('39', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0)
% 5.61/5.86          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.61/5.86             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.61/5.86      inference('simplify', [status(thm)], ['38'])).
% 5.61/5.86  thf(d10_xboole_0, axiom,
% 5.61/5.86    (![A:$i,B:$i]:
% 5.61/5.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.61/5.86  thf('40', plain,
% 5.61/5.86      (![X4 : $i, X6 : $i]:
% 5.61/5.86         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.61/5.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.61/5.86  thf('41', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 5.61/5.86               (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 5.61/5.86              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 5.61/5.86      inference('sup-', [status(thm)], ['39', '40'])).
% 5.61/5.86  thf('42', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (~ (v1_relat_1 @ X0)
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 5.61/5.86              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('sup-', [status(thm)], ['30', '41'])).
% 5.61/5.86  thf('43', plain,
% 5.61/5.86      (![X0 : $i, X1 : $i]:
% 5.61/5.86         (((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 5.61/5.86            = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 5.61/5.86          | ~ (v1_relat_1 @ X1)
% 5.61/5.86          | ~ (v1_relat_1 @ X0))),
% 5.61/5.86      inference('simplify', [status(thm)], ['42'])).
% 5.61/5.86  thf(t182_relat_1, conjecture,
% 5.61/5.86    (![A:$i]:
% 5.61/5.86     ( ( v1_relat_1 @ A ) =>
% 5.61/5.86       ( ![B:$i]:
% 5.61/5.86         ( ( v1_relat_1 @ B ) =>
% 5.61/5.86           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.61/5.86             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 5.61/5.86  thf(zf_stmt_0, negated_conjecture,
% 5.61/5.86    (~( ![A:$i]:
% 5.61/5.86        ( ( v1_relat_1 @ A ) =>
% 5.61/5.86          ( ![B:$i]:
% 5.61/5.86            ( ( v1_relat_1 @ B ) =>
% 5.61/5.86              ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.61/5.86                ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 5.61/5.86    inference('cnf.neg', [status(esa)], [t182_relat_1])).
% 5.61/5.86  thf('44', plain,
% 5.61/5.86      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 5.61/5.86         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 5.61/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.86  thf('45', plain,
% 5.61/5.86      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 5.61/5.86          != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 5.61/5.86        | ~ (v1_relat_1 @ sk_B)
% 5.61/5.86        | ~ (v1_relat_1 @ sk_A))),
% 5.61/5.86      inference('sup-', [status(thm)], ['43', '44'])).
% 5.61/5.86  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 5.61/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.86  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 5.61/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.86  thf('48', plain,
% 5.61/5.86      (((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 5.61/5.86         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 5.61/5.86      inference('demod', [status(thm)], ['45', '46', '47'])).
% 5.61/5.86  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 5.61/5.86  
% 5.61/5.86  % SZS output end Refutation
% 5.61/5.86  
% 5.61/5.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
