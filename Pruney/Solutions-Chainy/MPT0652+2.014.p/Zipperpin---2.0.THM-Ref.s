%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p8a8SayRUu

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 (  95 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  693 (1255 expanded)
%              Number of equality atoms :   58 ( 110 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ X4 )
       != ( k2_relat_1 @ X3 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('28',plain,
    ( ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('40',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['15','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p8a8SayRUu
% 0.15/0.37  % Computer   : n002.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 80 iterations in 0.095s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.55  thf(t78_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ A ) =>
% 0.23/0.55       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.23/0.55  thf('0', plain,
% 0.23/0.55      (![X10 : $i]:
% 0.23/0.55         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.23/0.55          | ~ (v1_relat_1 @ X10))),
% 0.23/0.55      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.23/0.55  thf(dt_k2_funct_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (![X11 : $i]:
% 0.23/0.55         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.23/0.55          | ~ (v1_funct_1 @ X11)
% 0.23/0.55          | ~ (v1_relat_1 @ X11))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.55  thf(t55_funct_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.55       ( ( v2_funct_1 @ A ) =>
% 0.23/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.23/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (![X14 : $i]:
% 0.23/0.55         (~ (v2_funct_1 @ X14)
% 0.23/0.55          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.23/0.55          | ~ (v1_funct_1 @ X14)
% 0.23/0.55          | ~ (v1_relat_1 @ X14))),
% 0.23/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.55  thf(t71_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.55  thf('3', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.55  thf(t199_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ A ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( v1_relat_1 @ B ) =>
% 0.23/0.55           ( ![C:$i]:
% 0.23/0.55             ( ( v1_relat_1 @ C ) =>
% 0.23/0.55               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.23/0.55                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.23/0.55                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X3)
% 0.23/0.55          | ((k2_relat_1 @ X4) != (k2_relat_1 @ X3))
% 0.23/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X5))
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ X3 @ X5)))
% 0.23/0.55          | ~ (v1_relat_1 @ X5)
% 0.23/0.55          | ~ (v1_relat_1 @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (((X0) != (k2_relat_1 @ X1))
% 0.23/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.55          | ~ (v1_relat_1 @ X2)
% 0.23/0.55          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.23/0.55          | ~ (v1_relat_1 @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.55  thf(fc3_funct_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.23/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.23/0.55  thf('6', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (((X0) != (k2_relat_1 @ X1))
% 0.23/0.55          | ~ (v1_relat_1 @ X2)
% 0.23/0.55          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.23/0.55          | ~ (v1_relat_1 @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X1 : $i, X2 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X1)
% 0.23/0.55          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.23/0.55          | ~ (v1_relat_1 @ X2))),
% 0.23/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.23/0.55            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X1)
% 0.23/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['2', '8'])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X1)
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['1', '9'])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.23/0.55            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X1)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k2_relat_1 @ X0)
% 0.23/0.55            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v2_funct_1 @ X0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['0', '11'])).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ((k2_relat_1 @ X0)
% 0.23/0.55              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.23/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.55  thf(t59_funct_1, conjecture,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.55       ( ( v2_funct_1 @ A ) =>
% 0.23/0.55         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.23/0.55             ( k2_relat_1 @ A ) ) & 
% 0.23/0.55           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.23/0.55             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i]:
% 0.23/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.55          ( ( v2_funct_1 @ A ) =>
% 0.23/0.55            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.23/0.55                ( k2_relat_1 @ A ) ) & 
% 0.23/0.55              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.23/0.55                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          != (k2_relat_1 @ sk_A))
% 0.23/0.55        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55            != (k2_relat_1 @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          != (k2_relat_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('split', [status(esa)], ['14'])).
% 0.23/0.55  thf('16', plain,
% 0.23/0.55      (![X14 : $i]:
% 0.23/0.55         (~ (v2_funct_1 @ X14)
% 0.23/0.55          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 0.23/0.55          | ~ (v1_funct_1 @ X14)
% 0.23/0.55          | ~ (v1_relat_1 @ X14))),
% 0.23/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.55  thf('17', plain,
% 0.23/0.55      (![X11 : $i]:
% 0.23/0.55         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.23/0.55          | ~ (v1_funct_1 @ X11)
% 0.23/0.55          | ~ (v1_relat_1 @ X11))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.55  thf(d10_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.55  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X14 : $i]:
% 0.23/0.55         (~ (v2_funct_1 @ X14)
% 0.23/0.55          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.23/0.55          | ~ (v1_funct_1 @ X14)
% 0.23/0.55          | ~ (v1_relat_1 @ X14))),
% 0.23/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.55  thf(t46_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ A ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( v1_relat_1 @ B ) =>
% 0.23/0.55           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.55             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X6)
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6)) = (k1_relat_1 @ X7))
% 0.23/0.55          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X6))
% 0.23/0.55          | ~ (v1_relat_1 @ X7))),
% 0.23/0.55      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.23/0.55              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.55          | ~ (v1_relat_1 @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X0)
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.23/0.55              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.23/0.55  thf('24', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.23/0.55              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.55          | ~ (v1_relat_1 @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.23/0.55              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.55          | ~ (v2_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['17', '24'])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (v2_funct_1 @ X0)
% 0.23/0.55          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.23/0.55              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          != (k2_relat_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('split', [status(esa)], ['14'])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      (((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.23/0.55         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.55         | ~ (v1_funct_1 @ sk_A)
% 0.23/0.55         | ~ (v2_funct_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.55  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('31', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.23/0.55         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.55         | ~ (v1_funct_1 @ sk_A)
% 0.23/0.55         | ~ (v2_funct_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['16', '32'])).
% 0.23/0.55  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('36', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('37', plain,
% 0.23/0.55      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.23/0.55         <= (~
% 0.23/0.55             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55                = (k2_relat_1 @ sk_A))))),
% 0.23/0.55      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.23/0.55  thf('38', plain,
% 0.23/0.55      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          = (k2_relat_1 @ sk_A)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.23/0.55  thf('39', plain,
% 0.23/0.55      (~
% 0.23/0.55       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          = (k2_relat_1 @ sk_A))) | 
% 0.23/0.55       ~
% 0.23/0.55       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          = (k2_relat_1 @ sk_A)))),
% 0.23/0.55      inference('split', [status(esa)], ['14'])).
% 0.23/0.55  thf('40', plain,
% 0.23/0.55      (~
% 0.23/0.55       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55          = (k2_relat_1 @ sk_A)))),
% 0.23/0.55      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.23/0.55  thf('41', plain,
% 0.23/0.55      (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.23/0.55         != (k2_relat_1 @ sk_A))),
% 0.23/0.55      inference('simpl_trail', [status(thm)], ['15', '40'])).
% 0.23/0.55  thf('42', plain,
% 0.23/0.55      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.23/0.55        | ~ (v1_relat_1 @ sk_A)
% 0.23/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.55        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['13', '41'])).
% 0.23/0.55  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('44', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('45', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('46', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.23/0.55  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
