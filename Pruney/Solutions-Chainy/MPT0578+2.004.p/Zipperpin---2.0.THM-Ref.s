%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0krMp641am

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:22 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   69 (  82 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  798 ( 953 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k10_relat_1 @ X21 @ ( k10_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X3 @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_E_1 @ X12 @ X8 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_E_1 @ X12 @ X8 @ X9 ) ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X9 )
      | ( r2_hidden @ X13 @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k10_relat_1 @ X21 @ ( k10_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

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

thf('42',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0krMp641am
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.92/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.14  % Solved by: fo/fo7.sh
% 0.92/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.14  % done 416 iterations in 0.700s
% 0.92/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.14  % SZS output start Refutation
% 0.92/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.92/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.14  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.92/1.14  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.92/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.92/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.14  thf(dt_k5_relat_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.92/1.14       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.92/1.14  thf('0', plain,
% 0.92/1.14      (![X15 : $i, X16 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X15)
% 0.92/1.14          | ~ (v1_relat_1 @ X16)
% 0.92/1.14          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.92/1.14      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.92/1.14  thf(t181_relat_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ B ) =>
% 0.92/1.14       ( ![C:$i]:
% 0.92/1.14         ( ( v1_relat_1 @ C ) =>
% 0.92/1.14           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.92/1.14             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.92/1.14  thf('1', plain,
% 0.92/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X20)
% 0.92/1.14          | ((k10_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.92/1.14              = (k10_relat_1 @ X21 @ (k10_relat_1 @ X20 @ X22)))
% 0.92/1.14          | ~ (v1_relat_1 @ X21))),
% 0.92/1.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.92/1.14  thf(t169_relat_1, axiom,
% 0.92/1.14    (![A:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ A ) =>
% 0.92/1.14       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.92/1.14  thf('2', plain,
% 0.92/1.14      (![X19 : $i]:
% 0.92/1.14         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.92/1.14          | ~ (v1_relat_1 @ X19))),
% 0.92/1.14      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.92/1.14  thf('3', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k10_relat_1 @ X1 @ 
% 0.92/1.14            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.92/1.14            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['1', '2'])).
% 0.92/1.14  thf('4', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ((k10_relat_1 @ X1 @ 
% 0.92/1.14              (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.92/1.14              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.92/1.14      inference('sup-', [status(thm)], ['0', '3'])).
% 0.92/1.14  thf('5', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k10_relat_1 @ X1 @ 
% 0.92/1.14            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.92/1.14            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['4'])).
% 0.92/1.14  thf(d3_tarski, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.14  thf('6', plain,
% 0.92/1.14      (![X1 : $i, X3 : $i]:
% 0.92/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf(d14_relat_1, axiom,
% 0.92/1.14    (![A:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ A ) =>
% 0.92/1.14       ( ![B:$i,C:$i]:
% 0.92/1.14         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.92/1.14           ( ![D:$i]:
% 0.92/1.14             ( ( r2_hidden @ D @ C ) <=>
% 0.92/1.14               ( ?[E:$i]:
% 0.92/1.14                 ( ( r2_hidden @ E @ B ) & 
% 0.92/1.14                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.92/1.14  thf('7', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.92/1.14         (((X11) != (k10_relat_1 @ X9 @ X8))
% 0.92/1.14          | (r2_hidden @ (sk_E_1 @ X12 @ X8 @ X9) @ X8)
% 0.92/1.14          | ~ (r2_hidden @ X12 @ X11)
% 0.92/1.14          | ~ (v1_relat_1 @ X9))),
% 0.92/1.14      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.92/1.14  thf('8', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X12 @ (k10_relat_1 @ X9 @ X8))
% 0.92/1.14          | (r2_hidden @ (sk_E_1 @ X12 @ X8 @ X9) @ X8))),
% 0.92/1.14      inference('simplify', [status(thm)], ['7'])).
% 0.92/1.14  thf('9', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.92/1.14          | (r2_hidden @ 
% 0.92/1.14             (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X0 @ X1) @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1))),
% 0.92/1.14      inference('sup-', [status(thm)], ['6', '8'])).
% 0.92/1.14  thf(t167_relat_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ B ) =>
% 0.92/1.14       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.92/1.14  thf('10', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.92/1.14          | ~ (v1_relat_1 @ X17))),
% 0.92/1.14      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.92/1.14  thf('11', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X0 @ X1)
% 0.92/1.14          | (r2_hidden @ X0 @ X2)
% 0.92/1.14          | ~ (r1_tarski @ X1 @ X2))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('12', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.92/1.14          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ X1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['10', '11'])).
% 0.92/1.14  thf('13', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X2)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X3)
% 0.92/1.14          | (r2_hidden @ 
% 0.92/1.14             (sk_E_1 @ 
% 0.92/1.14              (sk_C @ X3 @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.92/1.14              (k10_relat_1 @ X1 @ X0) @ X2) @ 
% 0.92/1.14             (k1_relat_1 @ X1))
% 0.92/1.14          | ~ (v1_relat_1 @ X1))),
% 0.92/1.14      inference('sup-', [status(thm)], ['9', '12'])).
% 0.92/1.14  thf('14', plain,
% 0.92/1.14      (![X1 : $i, X3 : $i]:
% 0.92/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('15', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.92/1.14         (((X11) != (k10_relat_1 @ X9 @ X8))
% 0.92/1.14          | (r2_hidden @ (k4_tarski @ X12 @ (sk_E_1 @ X12 @ X8 @ X9)) @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X12 @ X11)
% 0.92/1.14          | ~ (v1_relat_1 @ X9))),
% 0.92/1.14      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.92/1.14  thf('16', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X12 @ (k10_relat_1 @ X9 @ X8))
% 0.92/1.14          | (r2_hidden @ (k4_tarski @ X12 @ (sk_E_1 @ X12 @ X8 @ X9)) @ X9))),
% 0.92/1.14      inference('simplify', [status(thm)], ['15'])).
% 0.92/1.14  thf('17', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.92/1.14          | (r2_hidden @ 
% 0.92/1.14             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.92/1.14              (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.92/1.14             X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X1))),
% 0.92/1.14      inference('sup-', [status(thm)], ['14', '16'])).
% 0.92/1.14  thf('18', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.92/1.14         (((X11) != (k10_relat_1 @ X9 @ X8))
% 0.92/1.14          | (r2_hidden @ X13 @ X11)
% 0.92/1.14          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X14 @ X8)
% 0.92/1.14          | ~ (v1_relat_1 @ X9))),
% 0.92/1.14      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.92/1.14  thf('19', plain,
% 0.92/1.14      (![X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X14 @ X8)
% 0.92/1.14          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X9)
% 0.92/1.14          | (r2_hidden @ X13 @ (k10_relat_1 @ X9 @ X8)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['18'])).
% 0.92/1.14  thf('20', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.92/1.14             (k10_relat_1 @ X0 @ X3))
% 0.92/1.14          | ~ (r2_hidden @ 
% 0.92/1.14               (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ X1 @ X0) @ X3)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['17', '19'])).
% 0.92/1.14  thf('21', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (r2_hidden @ 
% 0.92/1.14             (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ X1 @ X0) @ X3)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.92/1.14             (k10_relat_1 @ X0 @ X3))
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['20'])).
% 0.92/1.14  thf('22', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ X3)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ X3)
% 0.92/1.14          | (r2_hidden @ 
% 0.92/1.14             (sk_C @ X3 @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2))) @ 
% 0.92/1.14             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.92/1.14      inference('sup-', [status(thm)], ['13', '21'])).
% 0.92/1.14  thf('23', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         ((r2_hidden @ 
% 0.92/1.14           (sk_C @ X3 @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2))) @ 
% 0.92/1.14           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ X3)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['22'])).
% 0.92/1.14  thf('24', plain,
% 0.92/1.14      (![X1 : $i, X3 : $i]:
% 0.92/1.14         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('25', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.92/1.14             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.92/1.14             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.92/1.14      inference('sup-', [status(thm)], ['23', '24'])).
% 0.92/1.14  thf('26', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X1)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.92/1.14             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['25'])).
% 0.92/1.14  thf('27', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.92/1.14           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1))),
% 0.92/1.14      inference('sup+', [status(thm)], ['5', '26'])).
% 0.92/1.14  thf('28', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.92/1.14             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.92/1.14      inference('simplify', [status(thm)], ['27'])).
% 0.92/1.14  thf('29', plain,
% 0.92/1.14      (![X19 : $i]:
% 0.92/1.14         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.92/1.14          | ~ (v1_relat_1 @ X19))),
% 0.92/1.14      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.92/1.14  thf('30', plain,
% 0.92/1.14      (![X15 : $i, X16 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X15)
% 0.92/1.14          | ~ (v1_relat_1 @ X16)
% 0.92/1.14          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.92/1.14      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.92/1.14  thf('31', plain,
% 0.92/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X20)
% 0.92/1.14          | ((k10_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.92/1.14              = (k10_relat_1 @ X21 @ (k10_relat_1 @ X20 @ X22)))
% 0.92/1.14          | ~ (v1_relat_1 @ X21))),
% 0.92/1.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.92/1.14  thf('32', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.92/1.14          | ~ (v1_relat_1 @ X17))),
% 0.92/1.14      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.92/1.14  thf('33', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.92/1.14           (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.92/1.14          | ~ (v1_relat_1 @ X2)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['31', '32'])).
% 0.92/1.14  thf('34', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.92/1.14             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.92/1.14      inference('sup-', [status(thm)], ['30', '33'])).
% 0.92/1.14  thf('35', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.92/1.14           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['34'])).
% 0.92/1.14  thf('36', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.92/1.14           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1))),
% 0.92/1.14      inference('sup+', [status(thm)], ['29', '35'])).
% 0.92/1.14  thf('37', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0)
% 0.92/1.14          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.92/1.14             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.92/1.14      inference('simplify', [status(thm)], ['36'])).
% 0.92/1.14  thf(d10_xboole_0, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.14  thf('38', plain,
% 0.92/1.14      (![X4 : $i, X6 : $i]:
% 0.92/1.14         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.14  thf('39', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.92/1.14               (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.92/1.14              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.92/1.14      inference('sup-', [status(thm)], ['37', '38'])).
% 0.92/1.14  thf('40', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X0)
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.92/1.14              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['28', '39'])).
% 0.92/1.14  thf('41', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.92/1.14            = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ X1)
% 0.92/1.14          | ~ (v1_relat_1 @ X0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.92/1.14  thf(t182_relat_1, conjecture,
% 0.92/1.14    (![A:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ A ) =>
% 0.92/1.14       ( ![B:$i]:
% 0.92/1.14         ( ( v1_relat_1 @ B ) =>
% 0.92/1.14           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.92/1.14             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.92/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.14    (~( ![A:$i]:
% 0.92/1.14        ( ( v1_relat_1 @ A ) =>
% 0.92/1.14          ( ![B:$i]:
% 0.92/1.14            ( ( v1_relat_1 @ B ) =>
% 0.92/1.14              ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.92/1.14                ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 0.92/1.14    inference('cnf.neg', [status(esa)], [t182_relat_1])).
% 0.92/1.14  thf('42', plain,
% 0.92/1.14      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.92/1.14         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('43', plain,
% 0.92/1.14      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.92/1.14          != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.92/1.14        | ~ (v1_relat_1 @ sk_B)
% 0.92/1.14        | ~ (v1_relat_1 @ sk_A))),
% 0.92/1.14      inference('sup-', [status(thm)], ['41', '42'])).
% 0.92/1.14  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('46', plain,
% 0.92/1.14      (((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.92/1.14         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.92/1.14      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.92/1.14  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.92/1.14  
% 0.92/1.14  % SZS output end Refutation
% 0.92/1.14  
% 0.92/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
