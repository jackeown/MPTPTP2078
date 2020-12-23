%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tpfuTTOH7w

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:29 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 120 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   20
%              Number of atoms          :  866 (1542 expanded)
%              Number of equality atoms :   75 ( 137 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ X7 )
       != ( k2_relat_1 @ X6 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t199_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X2 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

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

thf('18',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('39',plain,
    ( ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('51',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tpfuTTOH7w
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 78 iterations in 0.074s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.54  thf(d10_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.54  thf(t97_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.36/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.36/0.54          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf(dt_k2_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.36/0.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X16 : $i]:
% 0.36/0.54         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.36/0.54          | ~ (v1_funct_1 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.36/0.54  thf(t55_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) =>
% 0.36/0.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X19 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X19)
% 0.36/0.54          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 0.36/0.54          | ~ (v1_funct_1 @ X19)
% 0.36/0.54          | ~ (v1_relat_1 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf(t94_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.36/0.54          | ~ (v1_relat_1 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.36/0.54  thf(t71_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.54  thf('7', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.54  thf(t199_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v1_relat_1 @ B ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( v1_relat_1 @ C ) =>
% 0.36/0.54               ( ( ( k2_relat_1 @ A ) = ( k2_relat_1 @ B ) ) =>
% 0.36/0.54                 ( ( k2_relat_1 @ ( k5_relat_1 @ A @ C ) ) =
% 0.36/0.54                   ( k2_relat_1 @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X6)
% 0.36/0.54          | ((k2_relat_1 @ X7) != (k2_relat_1 @ X6))
% 0.36/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ X6 @ X8)))
% 0.36/0.54          | ~ (v1_relat_1 @ X8)
% 0.36/0.54          | ~ (v1_relat_1 @ X7))),
% 0.36/0.54      inference('cnf', [status(esa)], [t199_relat_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X0) != (k2_relat_1 @ X1))
% 0.36/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X2)
% 0.36/0.54          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf(fc3_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.36/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.36/0.54  thf('10', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X0) != (k2_relat_1 @ X1))
% 0.36/0.54          | ~ (v1_relat_1 @ X2)
% 0.36/0.54          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X1)
% 0.36/0.54          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X2))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X2)))
% 0.36/0.54          | ~ (v1_relat_1 @ X2))),
% 0.36/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.36/0.54            = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['6', '12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.36/0.54            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.36/0.54              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.36/0.54            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X1)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.54  thf(t59_funct_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) =>
% 0.36/0.54         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.36/0.54             ( k2_relat_1 @ A ) ) & 
% 0.36/0.54           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.36/0.54             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54          ( ( v2_funct_1 @ A ) =>
% 0.36/0.54            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.36/0.54                ( k2_relat_1 @ A ) ) & 
% 0.36/0.54              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.36/0.54                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          != (k2_relat_1 @ sk_A))
% 0.36/0.54        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54            != (k2_relat_1 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          != (k2_relat_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X19 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X19)
% 0.36/0.54          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 0.36/0.54          | ~ (v1_funct_1 @ X19)
% 0.36/0.54          | ~ (v1_relat_1 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X16 : $i]:
% 0.36/0.54         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.36/0.54          | ~ (v1_funct_1 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X16 : $i]:
% 0.36/0.54         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.36/0.54          | ~ (v1_funct_1 @ X16)
% 0.36/0.54          | ~ (v1_relat_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X19 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X19)
% 0.36/0.54          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 0.36/0.54          | ~ (v1_funct_1 @ X19)
% 0.36/0.54          | ~ (v1_relat_1 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf(t80_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X11 : $i]:
% 0.36/0.54         (((k5_relat_1 @ X11 @ (k6_relat_1 @ (k2_relat_1 @ X11))) = (X11))
% 0.36/0.54          | ~ (v1_relat_1 @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.36/0.54            = (k2_funct_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.36/0.54              = (k2_funct_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.36/0.54            = (k2_funct_1 @ X0))
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.54  thf('28', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.54  thf(t198_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v1_relat_1 @ B ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( v1_relat_1 @ C ) =>
% 0.36/0.54               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.36/0.54                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.36/0.54                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X3)
% 0.36/0.54          | ((k1_relat_1 @ X4) != (k1_relat_1 @ X3))
% 0.36/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ X5 @ X3)))
% 0.36/0.54          | ~ (v1_relat_1 @ X5)
% 0.36/0.54          | ~ (v1_relat_1 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X0) != (k1_relat_1 @ X1))
% 0.36/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X2)
% 0.36/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X0) != (k1_relat_1 @ X1))
% 0.36/0.54          | ~ (v1_relat_1 @ X2)
% 0.36/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X1)
% 0.36/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.36/0.54          | ~ (v1_relat_1 @ X2))),
% 0.36/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54            = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['27', '33'])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X0)
% 0.36/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.54              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['36'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          != (k2_relat_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.36/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.36/0.54         | ~ (v2_funct_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('42', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.36/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.36/0.54         | ~ (v2_funct_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '43'])).
% 0.36/0.54  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('46', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('47', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54                = (k2_relat_1 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          = (k2_relat_1 @ sk_A)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          = (k2_relat_1 @ sk_A))) | 
% 0.36/0.54       ~
% 0.36/0.54       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          = (k2_relat_1 @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54          = (k2_relat_1 @ sk_A)))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.36/0.54         != (k2_relat_1 @ sk_A))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['19', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((((k2_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)))
% 0.36/0.54          != (k2_relat_1 @ sk_A))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_A)
% 0.36/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['17', '52'])).
% 0.36/0.54  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('57', plain, ((v2_funct_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (((k2_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)))
% 0.36/0.54         != (k2_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '58'])).
% 0.36/0.54  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('61', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.54  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
