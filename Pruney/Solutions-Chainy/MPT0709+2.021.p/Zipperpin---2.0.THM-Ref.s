%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HxFPMGt7Gm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:08 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 659 expanded)
%              Number of leaves         :   20 ( 203 expanded)
%              Depth                    :   33
%              Number of atoms          : 1962 (7889 expanded)
%              Number of equality atoms :   74 ( 394 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','63'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('66',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57'])).

thf('67',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','76','77','78','79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('84',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('86',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('102',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('109',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ X2 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','119'])).

thf('121',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('125',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('126',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['123','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','147'])).

thf('149',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('150',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('151',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','80','163','164','165','166'])).

thf('168',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['174','175','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HxFPMGt7Gm
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.81/3.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.81/3.03  % Solved by: fo/fo7.sh
% 2.81/3.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.81/3.03  % done 4902 iterations in 2.612s
% 2.81/3.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.81/3.03  % SZS output start Refutation
% 2.81/3.03  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.81/3.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.81/3.03  thf(sk_B_type, type, sk_B: $i).
% 2.81/3.03  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.81/3.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.81/3.03  thf(sk_A_type, type, sk_A: $i).
% 2.81/3.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.81/3.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.81/3.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.81/3.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.81/3.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.81/3.03  thf(dt_k2_funct_1, axiom,
% 2.81/3.03    (![A:$i]:
% 2.81/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.81/3.03       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.81/3.03         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.81/3.03  thf('0', plain,
% 2.81/3.03      (![X9 : $i]:
% 2.81/3.03         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.03          | ~ (v1_funct_1 @ X9)
% 2.81/3.03          | ~ (v1_relat_1 @ X9))),
% 2.81/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.03  thf('1', plain,
% 2.81/3.03      (![X9 : $i]:
% 2.81/3.03         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 2.81/3.03          | ~ (v1_funct_1 @ X9)
% 2.81/3.03          | ~ (v1_relat_1 @ X9))),
% 2.81/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.03  thf(t164_funct_1, conjecture,
% 2.81/3.03    (![A:$i,B:$i]:
% 2.81/3.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.81/3.03       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.81/3.03         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.81/3.03  thf(zf_stmt_0, negated_conjecture,
% 2.81/3.03    (~( ![A:$i,B:$i]:
% 2.81/3.03        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.81/3.03          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.81/3.03            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 2.81/3.03    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 2.81/3.03  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.81/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.03  thf(t169_relat_1, axiom,
% 2.81/3.03    (![A:$i]:
% 2.81/3.03     ( ( v1_relat_1 @ A ) =>
% 2.81/3.03       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.81/3.03  thf('3', plain,
% 2.81/3.03      (![X5 : $i]:
% 2.81/3.03         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 2.81/3.03          | ~ (v1_relat_1 @ X5))),
% 2.81/3.03      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.81/3.03  thf(d10_xboole_0, axiom,
% 2.81/3.03    (![A:$i,B:$i]:
% 2.81/3.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.81/3.03  thf('4', plain,
% 2.81/3.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.81/3.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.81/3.03  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.81/3.03      inference('simplify', [status(thm)], ['4'])).
% 2.81/3.03  thf(t147_funct_1, axiom,
% 2.81/3.03    (![A:$i,B:$i]:
% 2.81/3.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.81/3.03       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 2.81/3.03         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.81/3.03  thf('6', plain,
% 2.81/3.03      (![X10 : $i, X11 : $i]:
% 2.81/3.03         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.03          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.03          | ~ (v1_funct_1 @ X11)
% 2.81/3.03          | ~ (v1_relat_1 @ X11))),
% 2.81/3.03      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.03  thf('7', plain,
% 2.81/3.03      (![X0 : $i]:
% 2.81/3.03         (~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.81/3.03              = (k2_relat_1 @ X0)))),
% 2.81/3.03      inference('sup-', [status(thm)], ['5', '6'])).
% 2.81/3.03  thf('8', plain,
% 2.81/3.03      (![X9 : $i]:
% 2.81/3.03         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.03          | ~ (v1_funct_1 @ X9)
% 2.81/3.03          | ~ (v1_relat_1 @ X9))),
% 2.81/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.03  thf(t154_funct_1, axiom,
% 2.81/3.03    (![A:$i,B:$i]:
% 2.81/3.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.81/3.03       ( ( v2_funct_1 @ B ) =>
% 2.81/3.03         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.81/3.03  thf('9', plain,
% 2.81/3.03      (![X12 : $i, X13 : $i]:
% 2.81/3.03         (~ (v2_funct_1 @ X12)
% 2.81/3.03          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.03              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.03          | ~ (v1_funct_1 @ X12)
% 2.81/3.03          | ~ (v1_relat_1 @ X12))),
% 2.81/3.03      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.03  thf(t167_relat_1, axiom,
% 2.81/3.03    (![A:$i,B:$i]:
% 2.81/3.03     ( ( v1_relat_1 @ B ) =>
% 2.81/3.03       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 2.81/3.03  thf('10', plain,
% 2.81/3.03      (![X3 : $i, X4 : $i]:
% 2.81/3.03         ((r1_tarski @ (k10_relat_1 @ X3 @ X4) @ (k1_relat_1 @ X3))
% 2.81/3.03          | ~ (v1_relat_1 @ X3))),
% 2.81/3.03      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.81/3.03  thf('11', plain,
% 2.81/3.03      (![X0 : $i, X1 : $i]:
% 2.81/3.03         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 2.81/3.03           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 2.81/3.03          | ~ (v1_relat_1 @ X1)
% 2.81/3.03          | ~ (v1_funct_1 @ X1)
% 2.81/3.03          | ~ (v2_funct_1 @ X1)
% 2.81/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 2.81/3.03      inference('sup+', [status(thm)], ['9', '10'])).
% 2.81/3.03  thf('12', plain,
% 2.81/3.03      (![X0 : $i, X1 : $i]:
% 2.81/3.03         (~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v2_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 2.81/3.03             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.81/3.03      inference('sup-', [status(thm)], ['8', '11'])).
% 2.81/3.03  thf('13', plain,
% 2.81/3.03      (![X0 : $i, X1 : $i]:
% 2.81/3.03         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 2.81/3.03           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.03          | ~ (v2_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0))),
% 2.81/3.03      inference('simplify', [status(thm)], ['12'])).
% 2.81/3.03  thf('14', plain,
% 2.81/3.03      (![X0 : $i]:
% 2.81/3.03         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v2_funct_1 @ X0))),
% 2.81/3.03      inference('sup+', [status(thm)], ['7', '13'])).
% 2.81/3.03  thf('15', plain,
% 2.81/3.03      (![X0 : $i]:
% 2.81/3.03         (~ (v2_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0)
% 2.81/3.03          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.81/3.03      inference('simplify', [status(thm)], ['14'])).
% 2.81/3.03  thf(t178_relat_1, axiom,
% 2.81/3.03    (![A:$i,B:$i,C:$i]:
% 2.81/3.03     ( ( v1_relat_1 @ C ) =>
% 2.81/3.03       ( ( r1_tarski @ A @ B ) =>
% 2.81/3.03         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.81/3.03  thf('16', plain,
% 2.81/3.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.03         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.03          | ~ (v1_relat_1 @ X8)
% 2.81/3.03          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.03      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.03  thf('17', plain,
% 2.81/3.03      (![X0 : $i, X1 : $i]:
% 2.81/3.03         (~ (v1_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v2_funct_1 @ X0)
% 2.81/3.03          | (r1_tarski @ (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 2.81/3.03             (k10_relat_1 @ X1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.81/3.03          | ~ (v1_relat_1 @ X1))),
% 2.81/3.03      inference('sup-', [status(thm)], ['15', '16'])).
% 2.81/3.03  thf('18', plain,
% 2.81/3.03      (![X0 : $i]:
% 2.81/3.03         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.81/3.03           (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v2_funct_1 @ X0)
% 2.81/3.03          | ~ (v1_relat_1 @ X0)
% 2.81/3.03          | ~ (v1_funct_1 @ X0))),
% 2.81/3.03      inference('sup+', [status(thm)], ['3', '17'])).
% 2.81/3.03  thf('19', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.81/3.04             (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 2.81/3.04      inference('simplify', [status(thm)], ['18'])).
% 2.81/3.04  thf('20', plain,
% 2.81/3.04      (![X3 : $i, X4 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ X3 @ X4) @ (k1_relat_1 @ X3))
% 2.81/3.04          | ~ (v1_relat_1 @ X3))),
% 2.81/3.04      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.81/3.04  thf('21', plain,
% 2.81/3.04      (![X0 : $i, X2 : $i]:
% 2.81/3.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.81/3.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.81/3.04  thf('22', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 2.81/3.04          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['20', '21'])).
% 2.81/3.04  thf('23', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ((k1_relat_1 @ X0)
% 2.81/3.04              = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['19', '22'])).
% 2.81/3.04  thf('24', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k1_relat_1 @ X0)
% 2.81/3.04            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['23'])).
% 2.81/3.04  thf('25', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('26', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('27', plain,
% 2.81/3.04      (![X5 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 2.81/3.04          | ~ (v1_relat_1 @ X5))),
% 2.81/3.04      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.81/3.04  thf('28', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.81/3.04              = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['5', '6'])).
% 2.81/3.04  thf('29', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup+', [status(thm)], ['27', '28'])).
% 2.81/3.04  thf('30', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('simplify', [status(thm)], ['29'])).
% 2.81/3.04  thf(t155_funct_1, axiom,
% 2.81/3.04    (![A:$i,B:$i]:
% 2.81/3.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.81/3.04       ( ( v2_funct_1 @ B ) =>
% 2.81/3.04         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.81/3.04  thf('31', plain,
% 2.81/3.04      (![X14 : $i, X15 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X14)
% 2.81/3.04          | ((k10_relat_1 @ X14 @ X15)
% 2.81/3.04              = (k9_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 2.81/3.04          | ~ (v1_funct_1 @ X14)
% 2.81/3.04          | ~ (v1_relat_1 @ X14))),
% 2.81/3.04      inference('cnf', [status(esa)], [t155_funct_1])).
% 2.81/3.04  thf('32', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0))),
% 2.81/3.04      inference('sup+', [status(thm)], ['30', '31'])).
% 2.81/3.04  thf('33', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['26', '32'])).
% 2.81/3.04  thf('34', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['33'])).
% 2.81/3.04  thf('35', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['25', '34'])).
% 2.81/3.04  thf('36', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['35'])).
% 2.81/3.04  thf('37', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0))),
% 2.81/3.04      inference('sup+', [status(thm)], ['24', '36'])).
% 2.81/3.04  thf('38', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.81/3.04      inference('simplify', [status(thm)], ['37'])).
% 2.81/3.04  thf('39', plain,
% 2.81/3.04      (![X10 : $i, X11 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.04          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.04          | ~ (v1_funct_1 @ X11)
% 2.81/3.04          | ~ (v1_relat_1 @ X11))),
% 2.81/3.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.04  thf('40', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.81/3.04          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.81/3.04              (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)) = (X1)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['38', '39'])).
% 2.81/3.04  thf('41', plain,
% 2.81/3.04      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['2', '40'])).
% 2.81/3.04  thf('42', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('43', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('simplify', [status(thm)], ['29'])).
% 2.81/3.04  thf('44', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('45', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('46', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('47', plain,
% 2.81/3.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.04          | ~ (v1_relat_1 @ X8)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.04      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.04  thf('48', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 2.81/3.04           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['46', '47'])).
% 2.81/3.04  thf('49', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 2.81/3.04           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.81/3.04      inference('sup+', [status(thm)], ['45', '48'])).
% 2.81/3.04  thf('50', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 2.81/3.04             (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['44', '49'])).
% 2.81/3.04  thf('51', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 2.81/3.04           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['50'])).
% 2.81/3.04  thf('52', plain,
% 2.81/3.04      (((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 2.81/3.04         (k2_relat_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['43', '51'])).
% 2.81/3.04  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('57', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('58', plain,
% 2.81/3.04      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 2.81/3.04        (k2_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['52', '53', '54', '55', '56', '57'])).
% 2.81/3.04  thf('59', plain,
% 2.81/3.04      (![X10 : $i, X11 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.04          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.04          | ~ (v1_funct_1 @ X11)
% 2.81/3.04          | ~ (v1_relat_1 @ X11))),
% 2.81/3.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.04  thf('60', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ((k9_relat_1 @ sk_B @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 2.81/3.04            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['58', '59'])).
% 2.81/3.04  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('63', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ 
% 2.81/3.04         (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 2.81/3.04         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.81/3.04  thf('64', plain,
% 2.81/3.04      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['42', '63'])).
% 2.81/3.04  thf('65', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('66', plain,
% 2.81/3.04      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 2.81/3.04        (k2_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['52', '53', '54', '55', '56', '57'])).
% 2.81/3.04  thf('67', plain,
% 2.81/3.04      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['65', '66'])).
% 2.81/3.04  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('70', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('71', plain,
% 2.81/3.04      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 2.81/3.04  thf('72', plain,
% 2.81/3.04      (![X10 : $i, X11 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.04          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.04          | ~ (v1_funct_1 @ X11)
% 2.81/3.04          | ~ (v1_relat_1 @ X11))),
% 2.81/3.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.04  thf('73', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ((k9_relat_1 @ sk_B @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04            = (k9_relat_1 @ sk_B @ sk_A)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['71', '72'])).
% 2.81/3.04  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('76', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04         = (k9_relat_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.81/3.04  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('80', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['64', '76', '77', '78', '79'])).
% 2.81/3.04  thf('81', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('82', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('83', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['35'])).
% 2.81/3.04  thf('84', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04         = (k9_relat_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.81/3.04  thf('85', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i]:
% 2.81/3.04         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 2.81/3.04           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['12'])).
% 2.81/3.04  thf('86', plain,
% 2.81/3.04      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ 
% 2.81/3.04         (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['84', '85'])).
% 2.81/3.04  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('89', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('90', plain,
% 2.81/3.04      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ 
% 2.81/3.04        (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 2.81/3.04  thf('91', plain,
% 2.81/3.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.04          | ~ (v1_relat_1 @ X8)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.04      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.04  thf('92', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04           (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['90', '91'])).
% 2.81/3.04  thf('93', plain,
% 2.81/3.04      (((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04         (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['83', '92'])).
% 2.81/3.04  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('95', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('96', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('98', plain,
% 2.81/3.04      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04        (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 2.81/3.04  thf('99', plain,
% 2.81/3.04      (![X10 : $i, X11 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.04          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.04          | ~ (v1_funct_1 @ X11)
% 2.81/3.04          | ~ (v1_relat_1 @ X11))),
% 2.81/3.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.04  thf('100', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 2.81/3.04            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['98', '99'])).
% 2.81/3.04  thf('101', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('102', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('103', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('simplify', [status(thm)], ['29'])).
% 2.81/3.04  thf('104', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('105', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.81/3.04              = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['5', '6'])).
% 2.81/3.04  thf('106', plain,
% 2.81/3.04      (![X9 : $i]:
% 2.81/3.04         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.81/3.04          | ~ (v1_funct_1 @ X9)
% 2.81/3.04          | ~ (v1_relat_1 @ X9))),
% 2.81/3.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.81/3.04  thf('107', plain,
% 2.81/3.04      (![X12 : $i, X13 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X12)
% 2.81/3.04          | ((k9_relat_1 @ X12 @ X13)
% 2.81/3.04              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.81/3.04          | ~ (v1_funct_1 @ X12)
% 2.81/3.04          | ~ (v1_relat_1 @ X12))),
% 2.81/3.04      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.81/3.04  thf('108', plain,
% 2.81/3.04      (![X3 : $i, X4 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ X3 @ X4) @ (k1_relat_1 @ X3))
% 2.81/3.04          | ~ (v1_relat_1 @ X3))),
% 2.81/3.04      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.81/3.04  thf('109', plain,
% 2.81/3.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.04          | ~ (v1_relat_1 @ X8)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.04      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.04  thf('110', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 2.81/3.04             (k10_relat_1 @ X2 @ (k1_relat_1 @ X0)))
% 2.81/3.04          | ~ (v1_relat_1 @ X2))),
% 2.81/3.04      inference('sup-', [status(thm)], ['108', '109'])).
% 2.81/3.04  thf('111', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         ((r1_tarski @ (k9_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.81/3.04           (k10_relat_1 @ (k2_funct_1 @ X2) @ (k1_relat_1 @ X1)))
% 2.81/3.04          | ~ (v1_relat_1 @ X2)
% 2.81/3.04          | ~ (v1_funct_1 @ X2)
% 2.81/3.04          | ~ (v2_funct_1 @ X2)
% 2.81/3.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X2))
% 2.81/3.04          | ~ (v1_relat_1 @ X1))),
% 2.81/3.04      inference('sup+', [status(thm)], ['107', '110'])).
% 2.81/3.04  thf('112', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X1)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X1 @ X2)) @ 
% 2.81/3.04             (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X1))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['106', '111'])).
% 2.81/3.04  thf('113', plain,
% 2.81/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.04         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ X1 @ X2)) @ 
% 2.81/3.04           (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X1)))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X1)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['112'])).
% 2.81/3.04  thf('114', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.81/3.04           (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0))),
% 2.81/3.04      inference('sup+', [status(thm)], ['105', '113'])).
% 2.81/3.04  thf('115', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.81/3.04             (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.81/3.04      inference('simplify', [status(thm)], ['114'])).
% 2.81/3.04  thf('116', plain,
% 2.81/3.04      (![X0 : $i, X2 : $i]:
% 2.81/3.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.81/3.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.81/3.04  thf('117', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (r1_tarski @ 
% 2.81/3.04               (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 2.81/3.04               (k2_relat_1 @ X0))
% 2.81/3.04          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04              = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['115', '116'])).
% 2.81/3.04  thf('118', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.81/3.04             (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04              = (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['104', '117'])).
% 2.81/3.04  thf('119', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04            = (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.81/3.04               (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('simplify', [status(thm)], ['118'])).
% 2.81/3.04  thf('120', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04              = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['103', '119'])).
% 2.81/3.04  thf('121', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.81/3.04      inference('simplify', [status(thm)], ['4'])).
% 2.81/3.04  thf('122', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04              = (k2_relat_1 @ X0)))),
% 2.81/3.04      inference('demod', [status(thm)], ['120', '121'])).
% 2.81/3.04  thf('123', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.81/3.04            = (k2_relat_1 @ X0))
% 2.81/3.04          | ~ (v2_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_funct_1 @ X0)
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('simplify', [status(thm)], ['122'])).
% 2.81/3.04  thf('124', plain,
% 2.81/3.04      (![X5 : $i]:
% 2.81/3.04         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 2.81/3.04          | ~ (v1_relat_1 @ X5))),
% 2.81/3.04      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.81/3.04  thf('125', plain,
% 2.81/3.04      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 2.81/3.04  thf('126', plain,
% 2.81/3.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.04          | ~ (v1_relat_1 @ X8)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.04      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.04  thf('127', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['125', '126'])).
% 2.81/3.04  thf('128', plain,
% 2.81/3.04      (((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04         (k1_relat_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['124', '127'])).
% 2.81/3.04  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('130', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('131', plain,
% 2.81/3.04      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 2.81/3.04        (k1_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['128', '129', '130'])).
% 2.81/3.04  thf('132', plain,
% 2.81/3.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X6 @ X7)
% 2.81/3.04          | ~ (v1_relat_1 @ X8)
% 2.81/3.04          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 2.81/3.04      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.81/3.04  thf('133', plain,
% 2.81/3.04      (![X0 : $i]:
% 2.81/3.04         ((r1_tarski @ 
% 2.81/3.04           (k10_relat_1 @ X0 @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 2.81/3.04           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 2.81/3.04          | ~ (v1_relat_1 @ X0))),
% 2.81/3.04      inference('sup-', [status(thm)], ['131', '132'])).
% 2.81/3.04  thf('134', plain,
% 2.81/3.04      (((r1_tarski @ 
% 2.81/3.04         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 2.81/3.04         (k2_relat_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('sup+', [status(thm)], ['123', '133'])).
% 2.81/3.04  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('136', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('137', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('138', plain,
% 2.81/3.04      (((r1_tarski @ 
% 2.81/3.04         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 2.81/3.04         (k2_relat_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 2.81/3.04  thf('139', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | (r1_tarski @ 
% 2.81/3.04           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 2.81/3.04           (k2_relat_1 @ sk_B)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['102', '138'])).
% 2.81/3.04  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('142', plain,
% 2.81/3.04      ((r1_tarski @ 
% 2.81/3.04        (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04         (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 2.81/3.04        (k2_relat_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['139', '140', '141'])).
% 2.81/3.04  thf('143', plain,
% 2.81/3.04      (![X10 : $i, X11 : $i]:
% 2.81/3.04         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 2.81/3.04          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 2.81/3.04          | ~ (v1_funct_1 @ X11)
% 2.81/3.04          | ~ (v1_relat_1 @ X11))),
% 2.81/3.04      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.81/3.04  thf('144', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ((k9_relat_1 @ sk_B @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ 
% 2.81/3.04             (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 2.81/3.04            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04               (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['142', '143'])).
% 2.81/3.04  thf('145', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('146', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('147', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ 
% 2.81/3.04         (k10_relat_1 @ sk_B @ 
% 2.81/3.04          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04           (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 2.81/3.04         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.81/3.04      inference('demod', [status(thm)], ['144', '145', '146'])).
% 2.81/3.04  thf('148', plain,
% 2.81/3.04      ((((k9_relat_1 @ sk_B @ 
% 2.81/3.04          (k10_relat_1 @ sk_B @ 
% 2.81/3.04           (k9_relat_1 @ sk_B @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 2.81/3.04          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 2.81/3.04        | ~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v2_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup+', [status(thm)], ['101', '147'])).
% 2.81/3.04  thf('149', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04         = (k9_relat_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.81/3.04  thf('150', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04         = (k9_relat_1 @ sk_B @ sk_A))),
% 2.81/3.04      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.81/3.04  thf('151', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('152', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('153', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('154', plain,
% 2.81/3.04      (((k9_relat_1 @ sk_B @ sk_A)
% 2.81/3.04         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 2.81/3.04            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.81/3.04      inference('demod', [status(thm)],
% 2.81/3.04                ['148', '149', '150', '151', '152', '153'])).
% 2.81/3.04  thf('155', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 2.81/3.04            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.81/3.04      inference('demod', [status(thm)], ['100', '154'])).
% 2.81/3.04  thf('156', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 2.81/3.04            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['82', '155'])).
% 2.81/3.04  thf('157', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('159', plain,
% 2.81/3.04      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 2.81/3.04          = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('demod', [status(thm)], ['156', '157', '158'])).
% 2.81/3.04  thf('160', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 2.81/3.04            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.81/3.04      inference('sup-', [status(thm)], ['81', '159'])).
% 2.81/3.04  thf('161', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('162', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('163', plain,
% 2.81/3.04      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 2.81/3.04         = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.81/3.04      inference('demod', [status(thm)], ['160', '161', '162'])).
% 2.81/3.04  thf('164', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('165', plain, ((v2_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('166', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('167', plain,
% 2.81/3.04      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 2.81/3.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('demod', [status(thm)],
% 2.81/3.04                ['41', '80', '163', '164', '165', '166'])).
% 2.81/3.04  thf('168', plain,
% 2.81/3.04      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('169', plain,
% 2.81/3.04      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('simplify_reflect-', [status(thm)], ['167', '168'])).
% 2.81/3.04  thf('170', plain,
% 2.81/3.04      ((~ (v1_relat_1 @ sk_B)
% 2.81/3.04        | ~ (v1_funct_1 @ sk_B)
% 2.81/3.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.81/3.04      inference('sup-', [status(thm)], ['1', '169'])).
% 2.81/3.04  thf('171', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('172', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('173', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 2.81/3.04      inference('demod', [status(thm)], ['170', '171', '172'])).
% 2.81/3.04  thf('174', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 2.81/3.04      inference('sup-', [status(thm)], ['0', '173'])).
% 2.81/3.04  thf('175', plain, ((v1_relat_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('176', plain, ((v1_funct_1 @ sk_B)),
% 2.81/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.04  thf('177', plain, ($false),
% 2.81/3.04      inference('demod', [status(thm)], ['174', '175', '176'])).
% 2.81/3.04  
% 2.81/3.04  % SZS output end Refutation
% 2.81/3.04  
% 2.81/3.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
