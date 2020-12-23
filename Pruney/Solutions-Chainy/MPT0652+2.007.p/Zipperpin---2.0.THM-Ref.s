%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7pzlAwnWf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  827 (1412 expanded)
%              Number of equality atoms :   71 ( 125 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('5',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
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

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ X8 )
       != ( k2_relat_1 @ X7 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
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
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('23',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
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
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

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
    inference('sup-',[status(thm)],['20','34'])).

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
    inference(split,[status(esa)],['17'])).

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
    inference('sup-',[status(thm)],['19','42'])).

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
    inference(split,[status(esa)],['17'])).

thf('50',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','51'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7pzlAwnWf
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:17:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 64 iterations in 0.072s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.53  thf(t77_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.53         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.22/0.53          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.22/0.53          | ~ (v1_relat_1 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf(dt_k2_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X15 : $i]:
% 0.22/0.53         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.22/0.53          | ~ (v1_funct_1 @ X15)
% 0.22/0.53          | ~ (v1_relat_1 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.53  thf(t55_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ A ) =>
% 0.22/0.53         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.22/0.53           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X16)
% 0.22/0.53          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 0.22/0.53          | ~ (v1_funct_1 @ X16)
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.53  thf(t71_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.53  thf('6', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.53  thf(t199_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( v1_relat_1 @ B ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( v1_relat_1 @ C ) =>
% 0.22/0.53               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.22/0.53                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.22/0.53                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X7)
% 0.22/0.53          | ((k2_relat_1 @ X8) != (k2_relat_1 @ X7))
% 0.22/0.53          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X9))
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.22/0.53          | ~ (v1_relat_1 @ X9)
% 0.22/0.53          | ~ (v1_relat_1 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((X0) != (k2_relat_1 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X2)
% 0.22/0.53          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.22/0.53          | ~ (v1_relat_1 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.53  thf('9', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((X0) != (k2_relat_1 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ X2)
% 0.22/0.53          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.22/0.53          | ~ (v1_relat_1 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X1)
% 0.22/0.53          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.22/0.53          | ~ (v1_relat_1 @ X2))),
% 0.22/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.22/0.53            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X1)
% 0.22/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['5', '11'])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X1)
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.22/0.53            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X1)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k2_relat_1 @ X0)
% 0.22/0.53            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k2_relat_1 @ X0)
% 0.22/0.53              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf(t59_funct_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ A ) =>
% 0.22/0.53         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.53             ( k2_relat_1 @ A ) ) & 
% 0.22/0.53           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.53             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53          ( ( v2_funct_1 @ A ) =>
% 0.22/0.53            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.53                ( k2_relat_1 @ A ) ) & 
% 0.22/0.53              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.53                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53          != (k2_relat_1 @ sk_A))
% 0.22/0.53        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53            != (k2_relat_1 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53          != (k2_relat_1 @ sk_A)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53                = (k2_relat_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X16)
% 0.22/0.53          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 0.22/0.53          | ~ (v1_funct_1 @ X16)
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X15 : $i]:
% 0.22/0.53         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.22/0.53          | ~ (v1_funct_1 @ X15)
% 0.22/0.53          | ~ (v1_relat_1 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X15 : $i]:
% 0.22/0.53         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.22/0.53          | ~ (v1_funct_1 @ X15)
% 0.22/0.53          | ~ (v1_relat_1 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X16)
% 0.22/0.53          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 0.22/0.53          | ~ (v1_funct_1 @ X16)
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.53  thf(t80_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X14 : $i]:
% 0.22/0.53         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.22/0.53          | ~ (v1_relat_1 @ X14))),
% 0.22/0.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.22/0.53            = (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.22/0.53              = (k2_funct_1 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.22/0.53            = (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.53  thf('27', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.53  thf(t198_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( v1_relat_1 @ B ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( v1_relat_1 @ C ) =>
% 0.22/0.53               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.22/0.53                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.22/0.53                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X4)
% 0.22/0.53          | ((k1_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.22/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ X6 @ X4)))
% 0.22/0.53          | ~ (v1_relat_1 @ X6)
% 0.22/0.53          | ~ (v1_relat_1 @ X5))),
% 0.22/0.53      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((X0) != (k1_relat_1 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X2)
% 0.22/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.22/0.53          | ~ (v1_relat_1 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf('30', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((X0) != (k1_relat_1 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ X2)
% 0.22/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.22/0.53          | ~ (v1_relat_1 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X1)
% 0.22/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.22/0.53          | ~ (v1_relat_1 @ X2))),
% 0.22/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53            = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['26', '32'])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v2_funct_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X0)
% 0.22/0.53          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.53              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53          != (k2_relat_1 @ sk_A)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53                = (k2_relat_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['17'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.22/0.53         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.53         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.53         | ~ (v2_funct_1 @ sk_A)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.53                = (k2_relat_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.53  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54                = (k2_relat_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.22/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.54         | ~ (v2_funct_1 @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54                = (k2_relat_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '42'])).
% 0.22/0.54  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54                = (k2_relat_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54          = (k2_relat_1 @ sk_A)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (~
% 0.22/0.54       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54          = (k2_relat_1 @ sk_A))) | 
% 0.22/0.54       ~
% 0.22/0.54       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54          = (k2_relat_1 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['17'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (~
% 0.22/0.54       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54          = (k2_relat_1 @ sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.54         != (k2_relat_1 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['18', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.54        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '51'])).
% 0.22/0.54  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('55', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('56', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.22/0.54  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
