%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUdqVqmMG1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:29 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   20
%              Number of atoms          :  830 (1418 expanded)
%              Number of equality atoms :   71 ( 125 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('2',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
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

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ X7 )
       != ( k2_relat_1 @ X6 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t59_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_1])).

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,
    ( ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','42'])).

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
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('50',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['15','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUdqVqmMG1
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 76 iterations in 0.073s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.56  thf(t78_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X11 : $i]:
% 0.38/0.56         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 0.38/0.56          | ~ (v1_relat_1 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.38/0.56  thf(dt_k2_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X14 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 0.38/0.56          | ~ (v1_funct_1 @ X14)
% 0.38/0.56          | ~ (v1_relat_1 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.56  thf(t55_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v2_funct_1 @ A ) =>
% 0.38/0.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X17)
% 0.38/0.56          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.56  thf(t71_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.56  thf('3', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t199_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( v1_relat_1 @ B ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( v1_relat_1 @ C ) =>
% 0.38/0.56               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.38/0.56                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.38/0.56                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X6)
% 0.38/0.56          | ((k2_relat_1 @ X7) != (k2_relat_1 @ X6))
% 0.38/0.56          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8))
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ X6 @ X8)))
% 0.38/0.56          | ~ (v1_relat_1 @ X8)
% 0.38/0.56          | ~ (v1_relat_1 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((X0) != (k2_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X2)
% 0.38/0.56          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf(fc4_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.56  thf('6', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((X0) != (k2_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ X2)
% 0.38/0.56          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.38/0.56          | ~ (v1_relat_1 @ X2))),
% 0.38/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.38/0.56            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.38/0.56            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k2_relat_1 @ X0)
% 0.38/0.56            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['0', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k2_relat_1 @ X0)
% 0.38/0.56              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.56  thf(t59_funct_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v2_funct_1 @ A ) =>
% 0.38/0.56         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.56             ( k2_relat_1 @ A ) ) & 
% 0.38/0.56           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.56             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56          ( ( v2_funct_1 @ A ) =>
% 0.38/0.56            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.56                ( k2_relat_1 @ A ) ) & 
% 0.38/0.56              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.56                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          != (k2_relat_1 @ sk_A))
% 0.38/0.56        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56            != (k2_relat_1 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          != (k2_relat_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X17)
% 0.38/0.56          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X14 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 0.38/0.56          | ~ (v1_funct_1 @ X14)
% 0.38/0.56          | ~ (v1_relat_1 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X14 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 0.38/0.56          | ~ (v1_funct_1 @ X14)
% 0.38/0.56          | ~ (v1_relat_1 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X17)
% 0.38/0.56          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.56  thf(d10_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.56  thf(t79_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.56         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.38/0.56          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 0.38/0.56          | ~ (v1_relat_1 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.38/0.56            = (k2_funct_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['19', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.38/0.56              = (k2_funct_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.38/0.56            = (k2_funct_1 @ X0))
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.56  thf('27', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t198_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( v1_relat_1 @ B ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( v1_relat_1 @ C ) =>
% 0.38/0.56               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.38/0.56                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.38/0.56                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X3)
% 0.38/0.56          | ((k1_relat_1 @ X4) != (k1_relat_1 @ X3))
% 0.38/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ X5 @ X3)))
% 0.38/0.56          | ~ (v1_relat_1 @ X5)
% 0.38/0.56          | ~ (v1_relat_1 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((X0) != (k1_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X2)
% 0.38/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((X0) != (k1_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ X2)
% 0.38/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_relat_1 @ X2))),
% 0.38/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56            = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['26', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56          | ~ (v2_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v2_funct_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X0)
% 0.38/0.56          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.56              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          != (k2_relat_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.38/0.56         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.56         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.56         | ~ (v2_funct_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.56  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.56         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.56         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.56         | ~ (v2_funct_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '42'])).
% 0.38/0.56  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56                = (k2_relat_1 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          = (k2_relat_1 @ sk_A)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (~
% 0.38/0.56       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          = (k2_relat_1 @ sk_A))) | 
% 0.38/0.56       ~
% 0.38/0.56       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          = (k2_relat_1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (~
% 0.38/0.56       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56          = (k2_relat_1 @ sk_A)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.56         != (k2_relat_1 @ sk_A))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['15', '50'])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.56        | ~ (v2_funct_1 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '51'])).
% 0.38/0.56  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('55', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('56', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.38/0.56  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
