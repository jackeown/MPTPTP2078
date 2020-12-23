%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jHyGftKOkE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:31 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 115 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   20
%              Number of atoms          :  831 (1504 expanded)
%              Number of equality atoms :   72 ( 134 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
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

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ X5 )
       != ( k2_relat_1 @ X4 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('15',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
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

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('36',plain,
    ( ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('48',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['16','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jHyGftKOkE
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 95 iterations in 0.141s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.61  thf(t98_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (![X12 : $i]:
% 0.43/0.61         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 0.43/0.61          | ~ (v1_relat_1 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.43/0.61  thf(dt_k2_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.43/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X13 : $i]:
% 0.43/0.61         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.43/0.61          | ~ (v1_funct_1 @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.43/0.61  thf(t55_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61       ( ( v2_funct_1 @ A ) =>
% 0.43/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.43/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X14 : $i]:
% 0.43/0.61         (~ (v2_funct_1 @ X14)
% 0.43/0.61          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.43/0.61          | ~ (v1_funct_1 @ X14)
% 0.43/0.61          | ~ (v1_relat_1 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.43/0.61  thf(t94_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i]:
% 0.43/0.61         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.43/0.61          | ~ (v1_relat_1 @ X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.43/0.61  thf(t71_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.61  thf('4', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf(t199_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( v1_relat_1 @ B ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( v1_relat_1 @ C ) =>
% 0.43/0.61               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.43/0.61                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.43/0.61                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X4)
% 0.43/0.61          | ((k2_relat_1 @ X5) != (k2_relat_1 @ X4))
% 0.43/0.61          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X6))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ X4 @ X6)))
% 0.43/0.61          | ~ (v1_relat_1 @ X6)
% 0.43/0.61          | ~ (v1_relat_1 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((X0) != (k2_relat_1 @ X1))
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X2)
% 0.43/0.61          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.43/0.61  thf('7', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((X0) != (k2_relat_1 @ X1))
% 0.43/0.61          | ~ (v1_relat_1 @ X2)
% 0.43/0.61          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X1)
% 0.43/0.61          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.43/0.61          | ~ (v1_relat_1 @ X2))),
% 0.43/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.43/0.61            = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['3', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.61            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['2', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.61              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '12'])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.61            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.43/0.61  thf(t59_funct_1, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61       ( ( v2_funct_1 @ A ) =>
% 0.43/0.61         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.43/0.61             ( k2_relat_1 @ A ) ) & 
% 0.43/0.61           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.43/0.61             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61          ( ( v2_funct_1 @ A ) =>
% 0.43/0.61            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.43/0.61                ( k2_relat_1 @ A ) ) & 
% 0.43/0.61              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.43/0.61                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          != (k2_relat_1 @ sk_A))
% 0.43/0.61        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61            != (k2_relat_1 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          != (k2_relat_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('split', [status(esa)], ['15'])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X14 : $i]:
% 0.43/0.61         (~ (v2_funct_1 @ X14)
% 0.43/0.61          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 0.43/0.61          | ~ (v1_funct_1 @ X14)
% 0.43/0.61          | ~ (v1_relat_1 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X13 : $i]:
% 0.43/0.61         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.43/0.61          | ~ (v1_funct_1 @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X13 : $i]:
% 0.43/0.61         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.43/0.61          | ~ (v1_funct_1 @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X14 : $i]:
% 0.43/0.61         (~ (v2_funct_1 @ X14)
% 0.43/0.61          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.43/0.61          | ~ (v1_funct_1 @ X14)
% 0.43/0.61          | ~ (v1_relat_1 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.43/0.61  thf(t80_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X9 : $i]:
% 0.43/0.61         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 0.43/0.61          | ~ (v1_relat_1 @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.43/0.61            = (k2_funct_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.43/0.61              = (k2_funct_1 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['19', '22'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.43/0.61            = (k2_funct_1 @ X0))
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.43/0.61  thf('25', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf(t198_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( v1_relat_1 @ B ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( v1_relat_1 @ C ) =>
% 0.43/0.61               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.43/0.61                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.43/0.61                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X1)
% 0.43/0.61          | ((k1_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.43/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ X3 @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X3)
% 0.43/0.61          | ~ (v1_relat_1 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((X0) != (k1_relat_1 @ X1))
% 0.43/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X2)
% 0.43/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.61  thf('28', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((X0) != (k1_relat_1 @ X1))
% 0.43/0.61          | ~ (v1_relat_1 @ X2)
% 0.43/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1))),
% 0.43/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X1)
% 0.43/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.43/0.61          | ~ (v1_relat_1 @ X2))),
% 0.43/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61            = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['24', '30'])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61          | ~ (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v2_funct_1 @ X0)
% 0.43/0.61          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.43/0.61              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          != (k2_relat_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('split', [status(esa)], ['15'])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.43/0.61         | ~ (v1_relat_1 @ sk_A)
% 0.43/0.61         | ~ (v1_funct_1 @ sk_A)
% 0.43/0.61         | ~ (v2_funct_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('39', plain, ((v2_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.43/0.61         | ~ (v1_relat_1 @ sk_A)
% 0.43/0.61         | ~ (v1_funct_1 @ sk_A)
% 0.43/0.61         | ~ (v2_funct_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['17', '40'])).
% 0.43/0.61  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('44', plain, ((v2_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61                = (k2_relat_1 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          = (k2_relat_1 @ sk_A)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (~
% 0.43/0.61       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          = (k2_relat_1 @ sk_A))) | 
% 0.43/0.61       ~
% 0.43/0.61       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          = (k2_relat_1 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['15'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (~
% 0.43/0.61       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61          = (k2_relat_1 @ sk_A)))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.43/0.61         != (k2_relat_1 @ sk_A))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['16', '48'])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      ((((k2_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)))
% 0.43/0.61          != (k2_relat_1 @ sk_A))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_A)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.43/0.61        | ~ (v2_funct_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '49'])).
% 0.43/0.61  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('54', plain, ((v2_funct_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (((k2_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)))
% 0.43/0.61         != (k2_relat_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '55'])).
% 0.43/0.61  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('58', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.43/0.61  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
