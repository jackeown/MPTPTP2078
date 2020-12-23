%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XY3yUvqppR

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:23 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 128 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   22
%              Number of atoms          :  970 (1690 expanded)
%              Number of equality atoms :   86 ( 152 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t198_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) )
                  = ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t58_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_funct_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t199_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k2_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
               => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) )
                  = ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ X10 )
       != ( k2_relat_1 @ X9 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('40',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('59',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XY3yUvqppR
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 110 iterations in 0.138s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.60  thf(d10_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.60  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.60      inference('simplify', [status(thm)], ['0'])).
% 0.40/0.60  thf(t79_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ B ) =>
% 0.40/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.40/0.60         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X14 : $i, X15 : $i]:
% 0.40/0.60         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.40/0.60          | ((k5_relat_1 @ X14 @ (k6_relat_1 @ X15)) = (X14))
% 0.40/0.60          | ~ (v1_relat_1 @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf(t71_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.40/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.60  thf('4', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.60  thf(dt_k2_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.60         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X18 : $i]:
% 0.40/0.60         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 0.40/0.60          | ~ (v1_funct_1 @ X18)
% 0.40/0.60          | ~ (v1_relat_1 @ X18))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.60  thf(t55_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v2_funct_1 @ A ) =>
% 0.40/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.40/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X21 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X21)
% 0.40/0.60          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.40/0.60          | ~ (v1_funct_1 @ X21)
% 0.40/0.60          | ~ (v1_relat_1 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.60  thf(t198_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( v1_relat_1 @ C ) =>
% 0.40/0.60               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.40/0.60                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.40/0.60                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X6)
% 0.40/0.60          | ((k1_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X8 @ X6)))
% 0.40/0.60          | ~ (v1_relat_1 @ X8)
% 0.40/0.60          | ~ (v1_relat_1 @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X0)))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X0)))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X0)))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((k2_relat_1 @ X1) != (X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_funct_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X1)))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0))))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ~ (v2_funct_1 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '10'])).
% 0.40/0.60  thf(fc4_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.40/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.40/0.60  thf('12', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((k2_relat_1 @ X1) != (X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_funct_1 @ X1)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X1)))
% 0.40/0.60              = (k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0))))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ~ (v2_funct_1 @ X1))),
% 0.40/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X1)))
% 0.40/0.60              = (k1_relat_1 @ 
% 0.40/0.60                 (k5_relat_1 @ X2 @ (k6_relat_1 @ (k2_relat_1 @ X1)))))
% 0.40/0.60          | ~ (v1_funct_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.40/0.60            = (k1_relat_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['3', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.40/0.60              = (k1_relat_1 @ X0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.40/0.60  thf(t58_funct_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v2_funct_1 @ A ) =>
% 0.40/0.60         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.40/0.60             ( k1_relat_1 @ A ) ) & 
% 0.40/0.60           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.40/0.60             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60          ( ( v2_funct_1 @ A ) =>
% 0.40/0.60            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.40/0.60                ( k1_relat_1 @ A ) ) & 
% 0.40/0.60              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.40/0.60                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          != (k1_relat_1 @ sk_A))
% 0.40/0.60        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60            != (k1_relat_1 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          != (k1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('split', [status(esa)], ['17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X21 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X21)
% 0.40/0.60          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 0.40/0.60          | ~ (v1_funct_1 @ X21)
% 0.40/0.60          | ~ (v1_relat_1 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X18 : $i]:
% 0.40/0.60         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 0.40/0.60          | ~ (v1_funct_1 @ X18)
% 0.40/0.60          | ~ (v1_relat_1 @ X18))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X18 : $i]:
% 0.40/0.60         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 0.40/0.60          | ~ (v1_funct_1 @ X18)
% 0.40/0.60          | ~ (v1_relat_1 @ X18))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X21 : $i]:
% 0.40/0.60         (~ (v2_funct_1 @ X21)
% 0.40/0.60          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.40/0.60          | ~ (v1_funct_1 @ X21)
% 0.40/0.60          | ~ (v1_relat_1 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.60  thf(t146_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X3 : $i]:
% 0.40/0.60         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.40/0.60          | ~ (v1_relat_1 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.60            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.60              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['21', '24'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.60            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.40/0.60          | ~ (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.60  thf(t148_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ B ) =>
% 0.40/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X4 : $i, X5 : $i]:
% 0.40/0.60         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.40/0.60          | ~ (v1_relat_1 @ X4))),
% 0.40/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.40/0.60  thf(t94_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ B ) =>
% 0.40/0.60       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]:
% 0.40/0.60         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 0.40/0.60          | ~ (v1_relat_1 @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.40/0.60  thf('29', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.60  thf(t199_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( v1_relat_1 @ C ) =>
% 0.40/0.60               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.40/0.60                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.40/0.60                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X9)
% 0.40/0.60          | ((k2_relat_1 @ X10) != (k2_relat_1 @ X9))
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X11))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X9 @ X11)))
% 0.40/0.60          | ~ (v1_relat_1 @ X11)
% 0.40/0.60          | ~ (v1_relat_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((X0) != (k2_relat_1 @ X1))
% 0.40/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('32', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((X0) != (k2_relat_1 @ X1))
% 0.40/0.60          | ~ (v1_relat_1 @ X2)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.40/0.60          | ~ (v1_relat_1 @ X2))),
% 0.40/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.40/0.60            = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['28', '34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k9_relat_1 @ X1 @ (k2_relat_1 @ X0))
% 0.40/0.60            = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['27', '36'])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0))
% 0.40/0.60              = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          != (k1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('split', [status(esa)], ['17'])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.40/0.60           != (k1_relat_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.40/0.60           != (k1_relat_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ sk_A)
% 0.40/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.40/0.60         | ~ (v2_funct_1 @ sk_A)
% 0.40/0.60         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['26', '42'])).
% 0.40/0.60  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (((~ (v1_relat_1 @ sk_A)
% 0.40/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.40/0.60         | ((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['20', '47'])).
% 0.40/0.60  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('50', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      ((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.40/0.60         | ~ (v1_relat_1 @ sk_A)
% 0.40/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.40/0.60         | ~ (v2_funct_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '51'])).
% 0.40/0.60  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('55', plain, ((v2_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60                = (k1_relat_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          = (k1_relat_1 @ sk_A)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          = (k1_relat_1 @ sk_A))) | 
% 0.40/0.60       ~
% 0.40/0.60       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          = (k1_relat_1 @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['17'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60          = (k1_relat_1 @ sk_A)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.40/0.60         != (k1_relat_1 @ sk_A))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['18', '59'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.40/0.60        | ~ (v1_relat_1 @ sk_A)
% 0.40/0.60        | ~ (v1_funct_1 @ sk_A)
% 0.40/0.60        | ~ (v2_funct_1 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '60'])).
% 0.40/0.60  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('63', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('64', plain, ((v2_funct_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('65', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.40/0.60  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
