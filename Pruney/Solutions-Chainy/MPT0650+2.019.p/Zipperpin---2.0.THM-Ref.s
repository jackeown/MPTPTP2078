%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wITXtgeplU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:21 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 238 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          : 1126 (3471 expanded)
%              Number of equality atoms :   75 ( 244 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_funct_1 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('7',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X21 @ X22 ) @ X23 )
        = ( k1_funct_1 @ X22 @ ( k1_funct_1 @ X21 @ X23 ) ) )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) @ X1 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('36',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['34','36'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_funct_1 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['34','36'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ( X25
        = ( k1_funct_1 @ ( k2_funct_1 @ X24 ) @ ( k1_funct_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('54',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','60'])).

thf('62',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['30','31','32','33','61'])).

thf('63',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_funct_1 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('64',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('72',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('75',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('78',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wITXtgeplU
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 150 iterations in 0.162s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.44/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.44/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.44/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.44/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.62  thf(t57_funct_1, conjecture,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.44/0.62         ( ( ( A ) =
% 0.44/0.62             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.44/0.62           ( ( A ) =
% 0.44/0.62             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i]:
% 0.44/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.44/0.62            ( ( ( A ) =
% 0.44/0.62                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.44/0.62              ( ( A ) =
% 0.44/0.62                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.44/0.62  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_k4_relat_1, axiom,
% 0.44/0.62    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.44/0.62  thf(d9_funct_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X17 : $i]:
% 0.44/0.62         (~ (v2_funct_1 @ X17)
% 0.44/0.62          | ((k2_funct_1 @ X17) = (k4_relat_1 @ X17))
% 0.44/0.62          | ~ (v1_funct_1 @ X17)
% 0.44/0.62          | ~ (v1_relat_1 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.44/0.62  thf(dt_k2_funct_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.44/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X18 : $i]:
% 0.44/0.62         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 0.44/0.62          | ~ (v1_funct_1 @ X18)
% 0.44/0.62          | ~ (v1_relat_1 @ X18))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.62  thf(t37_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ A ) =>
% 0.44/0.62       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.44/0.62         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X13 : $i]:
% 0.44/0.62         (((k2_relat_1 @ X13) = (k1_relat_1 @ (k4_relat_1 @ X13)))
% 0.44/0.62          | ~ (v1_relat_1 @ X13))),
% 0.44/0.62      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X13 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X13) = (k2_relat_1 @ (k4_relat_1 @ X13)))
% 0.44/0.62          | ~ (v1_relat_1 @ X13))),
% 0.44/0.62      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.44/0.62  thf(t80_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ A ) =>
% 0.44/0.62       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X16 : $i]:
% 0.44/0.62         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 0.44/0.62          | ~ (v1_relat_1 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.44/0.62  thf(t182_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( v1_relat_1 @ B ) =>
% 0.44/0.62           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.44/0.62             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X8)
% 0.44/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.44/0.62              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.44/0.62          | ~ (v1_relat_1 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X0)
% 0.44/0.62            = (k10_relat_1 @ X0 @ 
% 0.44/0.62               (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf(t71_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.44/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.44/0.62  thf('11', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.44/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.44/0.62  thf(fc4_funct_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.44/0.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.62  thf('12', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62            = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['7', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62              = (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 0.44/0.62      inference('clc', [status(thm)], ['15', '16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X8)
% 0.44/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.44/0.62              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.44/0.62          | ~ (v1_relat_1 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.44/0.62  thf(t22_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62       ( ![C:$i]:
% 0.44/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.44/0.62             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.44/0.62               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X21)
% 0.44/0.62          | ~ (v1_funct_1 @ X21)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X21 @ X22) @ X23)
% 0.44/0.62              = (k1_funct_1 @ X22 @ (k1_funct_1 @ X21 @ X23)))
% 0.44/0.62          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ (k5_relat_1 @ X21 @ X22)))
% 0.44/0.62          | ~ (v1_funct_1 @ X22)
% 0.44/0.62          | ~ (v1_relat_1 @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.44/0.62          | ~ (v1_relat_1 @ X1)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.44/0.62          | ~ (v1_funct_1 @ X1)
% 0.44/0.62          | ~ (v1_relat_1 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (v1_funct_1 @ X1)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X1)
% 0.44/0.62          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '21'])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '25'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.44/0.62          | ~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.44/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '27'])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0) @ X1)
% 0.44/0.62            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ X0) @ X1)))
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.44/0.62          | ~ (v2_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ~ (v1_relat_1 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.44/0.62        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.44/0.62            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '29'])).
% 0.44/0.62  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('34', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d5_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.44/0.62       ( ![C:$i]:
% 0.44/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.44/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.44/0.62          | ((X3) != (k2_relat_1 @ X2)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (![X2 : $i, X4 : $i]:
% 0.44/0.62         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.44/0.62          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '36'])).
% 0.44/0.62  thf(t8_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.44/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.44/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.44/0.62          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.44/0.62          | ~ (v1_funct_1 @ X27)
% 0.44/0.62          | ~ (v1_relat_1 @ X27))),
% 0.44/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.62  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X17 : $i]:
% 0.44/0.62         (~ (v2_funct_1 @ X17)
% 0.44/0.62          | ((k2_funct_1 @ X17) = (k4_relat_1 @ X17))
% 0.44/0.62          | ~ (v1_funct_1 @ X17)
% 0.44/0.62          | ~ (v1_relat_1 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '36'])).
% 0.44/0.62  thf(t20_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ C ) =>
% 0.44/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.44/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.44/0.62           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.44/0.62          | (r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.44/0.62          | ~ (v1_relat_1 @ X12))),
% 0.44/0.62      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.62  thf(t56_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.44/0.62         ( ( ( A ) =
% 0.44/0.62             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.44/0.62           ( ( A ) =
% 0.44/0.62             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i]:
% 0.44/0.62         (~ (v2_funct_1 @ X24)
% 0.44/0.62          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.44/0.62          | ((X25)
% 0.44/0.62              = (k1_funct_1 @ (k2_funct_1 @ X24) @ (k1_funct_1 @ X24 @ X25)))
% 0.44/0.62          | ~ (v1_funct_1 @ X24)
% 0.44/0.62          | ~ (v1_relat_1 @ X24))),
% 0.44/0.62      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62        | ((sk_D_1 @ sk_A @ sk_B)
% 0.44/0.62            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.44/0.62               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.44/0.62        | ~ (v2_funct_1 @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.62  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('53', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.62  thf('54', plain, ((v2_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('55', plain,
% 0.44/0.62      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62        | ~ (v2_funct_1 @ sk_B))),
% 0.44/0.62      inference('sup+', [status(thm)], ['43', '55'])).
% 0.44/0.62  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('59', plain, ((v2_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      (((sk_A)
% 0.44/0.62         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['42', '60'])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.44/0.62         = (sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['30', '31', '32', '33', '61'])).
% 0.44/0.62  thf('63', plain,
% 0.44/0.62      (![X17 : $i]:
% 0.44/0.62         (~ (v2_funct_1 @ X17)
% 0.44/0.62          | ((k2_funct_1 @ X17) = (k4_relat_1 @ X17))
% 0.44/0.62          | ~ (v1_funct_1 @ X17)
% 0.44/0.62          | ~ (v1_relat_1 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.44/0.62  thf('64', plain,
% 0.44/0.62      ((((sk_A)
% 0.44/0.62          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.44/0.62        | ((sk_A)
% 0.44/0.62            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('65', plain,
% 0.44/0.62      ((((sk_A)
% 0.44/0.62          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.44/0.62                   sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['64'])).
% 0.44/0.62  thf('66', plain,
% 0.44/0.62      (((((sk_A)
% 0.44/0.62           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.44/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.44/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62         | ~ (v2_funct_1 @ sk_B)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.44/0.62                   sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['63', '65'])).
% 0.44/0.62  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      ((((sk_A)
% 0.44/0.62          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.44/0.62                   sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.44/0.62  thf('71', plain,
% 0.44/0.62      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.44/0.62  thf('72', plain,
% 0.44/0.62      ((((sk_A)
% 0.44/0.62          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ sk_B @ 
% 0.44/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.44/0.62      inference('split', [status(esa)], ['64'])).
% 0.44/0.62  thf('73', plain,
% 0.44/0.62      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ sk_B @ 
% 0.44/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('74', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.62  thf('75', plain,
% 0.44/0.62      ((((sk_A) != (sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((sk_A)
% 0.44/0.62                = (k1_funct_1 @ sk_B @ 
% 0.44/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.44/0.62  thf('76', plain,
% 0.44/0.62      ((((sk_A)
% 0.44/0.62          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['75'])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((sk_A)
% 0.44/0.62          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.44/0.62       ~
% 0.44/0.62       (((sk_A)
% 0.44/0.62          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['64'])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((sk_A)
% 0.44/0.62          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.44/0.62  thf('79', plain,
% 0.44/0.62      (((sk_A)
% 0.44/0.62         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['70', '78'])).
% 0.44/0.62  thf('80', plain, ($false),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['62', '79'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
