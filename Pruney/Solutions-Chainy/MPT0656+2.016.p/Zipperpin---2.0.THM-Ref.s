%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wo0wVOHA1C

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:38 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  342 (10407 expanded)
%              Number of leaves         :   25 (3308 expanded)
%              Depth                    :   38
%              Number of atoms          : 3059 (132990 expanded)
%              Number of equality atoms :  176 (12602 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t63_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('2',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('4',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('6',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','36'])).

thf('38',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('44',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('63',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','65','66','67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('71',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('77',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('83',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('84',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','90'])).

thf('92',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('95',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('97',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','100'])).

thf('102',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['93','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','115','116','117','118'])).

thf('120',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('121',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('122',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('124',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('130',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('132',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('134',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('141',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('142',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('145',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','146','147','148','149'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('152',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('153',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','119','150','156'])).

thf('158',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('161',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','160','161','162','163'])).

thf('165',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','115','116','117','118'])).

thf('168',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','169'])).

thf('171',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('172',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('174',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('175',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('177',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['179','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('195',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('197',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('199',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('200',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['174','200'])).

thf('202',plain,
    ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('204',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','203','204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['173','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) )
      = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('219',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','203','204','205'])).

thf('220',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('221',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('222',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('228',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['216','217','218','219','228'])).

thf('230',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['172','229'])).

thf('231',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('232',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('233',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['177','178'])).

thf('234',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('237',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('244',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('250',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('251',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['248','252'])).

thf('254',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('255',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['242','257'])).

thf('259',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['232','258'])).

thf('260',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('261',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','115','116','117','118'])).

thf('265',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['259','260','261','262','263','264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('267',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('269',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('271',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['267','268','269','270'])).

thf('272',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['230','231','271','272','273','274'])).

thf('276',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('277',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['275','276'])).

thf('278',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('279',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['171','280'])).

thf('282',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('285',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('289',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('293',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['285','286'])).

thf('294',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('295',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['285','286'])).

thf('296',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['289','290','291','292','293','294','295'])).

thf('297',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['285','286'])).

thf('298',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('299',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['297','298'])).

thf('300',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('301',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('302',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['299','300','301','302'])).

thf('304',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['296','303'])).

thf('305',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('306',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['296','303'])).

thf('308',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('310',plain,
    ( sk_B
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['306','307','308','309'])).

thf('311',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('312',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['170','310','311','312'])).

thf('314',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['313','314'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wo0wVOHA1C
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:38:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 579 iterations in 0.491s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.77/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.96  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.77/0.96  thf(t63_funct_1, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/0.96           ( ( ( v2_funct_1 @ A ) & 
% 0.77/0.96               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.77/0.96               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.77/0.96             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/0.96              ( ( ( v2_funct_1 @ A ) & 
% 0.77/0.96                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.77/0.96                  ( ( k5_relat_1 @ A @ B ) =
% 0.77/0.96                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.77/0.96                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t146_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.77/0.96          | ~ (v1_relat_1 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t71_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.77/0.96       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.77/0.96  thf('3', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.77/0.96  thf(t160_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.77/0.96             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      ((((k1_relat_1 @ sk_A) = (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf('7', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (((k1_relat_1 @ sk_A) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B)) | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['1', '10'])).
% 0.77/0.96  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('13', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.77/0.96      inference('demod', [status(thm)], ['0', '13'])).
% 0.77/0.96  thf(t61_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v2_funct_1 @ A ) =>
% 0.77/0.96         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.77/0.96             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.77/0.96           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.77/0.96             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (![X19 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X19)
% 0.77/0.96          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.77/0.96              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.77/0.96          | ~ (v1_funct_1 @ X19)
% 0.77/0.96          | ~ (v1_relat_1 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.77/0.96  thf('16', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t80_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('18', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.77/0.96            = (k6_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['18', '19'])).
% 0.77/0.96  thf(fc3_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.77/0.96       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.77/0.96  thf('21', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.77/0.96           = (k6_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.77/0.96  thf(t44_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( r1_tarski @
% 0.77/0.96             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X5)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.77/0.96             (k1_relat_1 @ X6))
% 0.77/0.96          | ~ (v1_relat_1 @ X6))),
% 0.77/0.96      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.77/0.96           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['22', '23'])).
% 0.77/0.96  thf('25', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('26', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('27', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('28', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.77/0.96      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.77/0.96  thf(t77_relat_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ B ) =>
% 0.77/0.96       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.77/0.96         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      (![X12 : $i, X13 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.77/0.96          | ~ (v1_relat_1 @ X12))),
% 0.77/0.96      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf(t55_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_relat_1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v1_relat_1 @ B ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( v1_relat_1 @ C ) =>
% 0.77/0.96               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.77/0.96                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X0 @ X1)
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.77/0.96               (k5_relat_1 @ X0 @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X0 @ X1)
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.77/0.96               (k5_relat_1 @ X0 @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['33', '34'])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ X0 @ X1)
% 0.77/0.96              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.77/0.96                 (k5_relat_1 @ X0 @ X1))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['35'])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['17', '36'])).
% 0.77/0.96  thf('38', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.77/0.96              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['39'])).
% 0.77/0.96  thf(dt_k2_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.77/0.96         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf(t55_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v2_funct_1 @ A ) =>
% 0.77/0.96         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.77/0.96           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X18 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X18)
% 0.77/0.96          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 0.77/0.96          | ~ (v1_funct_1 @ X18)
% 0.77/0.96          | ~ (v1_relat_1 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96            = (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96              = (k2_funct_1 @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['42', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96            = (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf(dt_k5_relat_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.77/0.96       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['48', '49'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['47', '51'])).
% 0.77/0.96  thf('53', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X1))),
% 0.77/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['54'])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['41', '55'])).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['56'])).
% 0.77/0.96  thf('58', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96            (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['40', '57'])).
% 0.77/0.96  thf('59', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['58'])).
% 0.77/0.96  thf('60', plain,
% 0.77/0.96      (((v1_relat_1 @ 
% 0.77/0.96         (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 0.77/0.96          (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['16', '59'])).
% 0.77/0.96  thf('61', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('62', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      ((((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['61', '62'])).
% 0.77/0.96  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('65', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['63', '64'])).
% 0.77/0.96  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('67', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('68', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('69', plain, ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['60', '65', '66', '67', '68'])).
% 0.77/0.96  thf('70', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('71', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('72', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.77/0.96            = (k5_relat_1 @ X0 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['70', '71'])).
% 0.77/0.96  thf('73', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96        | ((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A) @ 
% 0.77/0.96            (k6_relat_1 @ 
% 0.77/0.96             (k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))))
% 0.77/0.96            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['69', '72'])).
% 0.77/0.96  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('75', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('76', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('77', plain,
% 0.77/0.96      (![X18 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X18)
% 0.77/0.96          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.77/0.96          | ~ (v1_funct_1 @ X18)
% 0.77/0.96          | ~ (v1_relat_1 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('78', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('79', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.77/0.96           = (k6_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.77/0.96  thf('80', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['50'])).
% 0.77/0.96  thf('81', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/0.96  thf('82', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('83', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('84', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('85', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.77/0.96            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X1))),
% 0.77/0.96      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.77/0.96  thf('86', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['78', '85'])).
% 0.77/0.96  thf('87', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['86'])).
% 0.77/0.96  thf('88', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['77', '87'])).
% 0.77/0.96  thf('89', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['76', '88'])).
% 0.77/0.96  thf('90', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['89'])).
% 0.77/0.96  thf('91', plain,
% 0.77/0.96      (((v1_relat_1 @ 
% 0.77/0.96         (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['75', '90'])).
% 0.77/0.96  thf('92', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('93', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('94', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96            = (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.77/0.96  thf('95', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('96', plain,
% 0.77/0.96      (![X18 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X18)
% 0.77/0.96          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.77/0.96          | ~ (v1_funct_1 @ X18)
% 0.77/0.96          | ~ (v1_relat_1 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('97', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X5)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.77/0.96             (k1_relat_1 @ X6))
% 0.77/0.96          | ~ (v1_relat_1 @ X6))),
% 0.77/0.96      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.77/0.96  thf('98', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.77/0.96           (k2_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['96', '97'])).
% 0.77/0.96  thf('99', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (r1_tarski @ 
% 0.77/0.96             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.77/0.96             (k2_relat_1 @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['95', '98'])).
% 0.77/0.96  thf('100', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.77/0.96           (k2_relat_1 @ X0))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['99'])).
% 0.77/0.96  thf('101', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96          | ~ (v2_funct_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['94', '100'])).
% 0.77/0.96  thf('102', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('103', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v2_funct_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['101', '102'])).
% 0.77/0.96  thf('104', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['103'])).
% 0.77/0.96  thf('105', plain,
% 0.77/0.96      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_A)) @ (k1_relat_1 @ sk_B))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['93', '104'])).
% 0.77/0.96  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('107', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('108', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('109', plain,
% 0.77/0.96      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_A)) @ (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.77/0.96  thf('110', plain,
% 0.77/0.96      (![X12 : $i, X13 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.77/0.96          | ~ (v1_relat_1 @ X12))),
% 0.77/0.96      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.77/0.96  thf('111', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/0.96            (k2_funct_1 @ sk_A)) = (k2_funct_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['109', '110'])).
% 0.77/0.96  thf('112', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/0.96            (k2_funct_1 @ sk_A)) = (k2_funct_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['92', '111'])).
% 0.77/0.96  thf('113', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('114', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('115', plain,
% 0.77/0.96      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 0.77/0.96         = (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.77/0.96  thf('116', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('117', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('118', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('119', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['91', '115', '116', '117', '118'])).
% 0.77/0.96  thf('120', plain,
% 0.77/0.96      (![X18 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X18)
% 0.77/0.96          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 0.77/0.96          | ~ (v1_funct_1 @ X18)
% 0.77/0.96          | ~ (v1_relat_1 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('121', plain,
% 0.77/0.96      (![X15 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.77/0.96          | ~ (v1_funct_1 @ X15)
% 0.77/0.96          | ~ (v1_relat_1 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('122', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('123', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.77/0.96            = (k2_funct_1 @ X0))
% 0.77/0.96          | ~ (v2_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.77/0.96  thf('124', plain,
% 0.77/0.96      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.77/0.96          = (k2_funct_1 @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['122', '123'])).
% 0.77/0.96  thf('125', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('126', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('127', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('128', plain,
% 0.77/0.96      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.77/0.96         = (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.77/0.96  thf('129', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.77/0.96      inference('demod', [status(thm)], ['0', '13'])).
% 0.77/0.96  thf('130', plain,
% 0.77/0.96      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96         = (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['128', '129'])).
% 0.77/0.96  thf('131', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('132', plain,
% 0.77/0.96      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96             (k2_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.77/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['130', '131'])).
% 0.77/0.96  thf('133', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('134', plain,
% 0.77/0.96      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96             (k2_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.77/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['132', '133'])).
% 0.77/0.96  thf('135', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96            = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96               (k2_relat_1 @ (k2_funct_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['121', '134'])).
% 0.77/0.96  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('137', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('138', plain,
% 0.77/0.96      (((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96         = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96            (k2_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.77/0.96  thf('139', plain,
% 0.77/0.96      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96             (k1_relat_1 @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['120', '138'])).
% 0.77/0.96  thf('140', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('141', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('142', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.77/0.96          | ~ (v1_relat_1 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.77/0.96  thf('143', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.77/0.96            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['141', '142'])).
% 0.77/0.96  thf('144', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('145', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('146', plain,
% 0.77/0.96      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.77/0.96  thf('147', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('148', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('149', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('150', plain,
% 0.77/0.96      (((k2_relat_1 @ (k2_funct_1 @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['139', '140', '146', '147', '148', '149'])).
% 0.77/0.96  thf('151', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('152', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.77/0.96          | ~ (v1_relat_1 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.77/0.96  thf('153', plain,
% 0.77/0.96      ((((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['151', '152'])).
% 0.77/0.96  thf('154', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('155', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('156', plain,
% 0.77/0.96      (((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.77/0.96  thf('157', plain,
% 0.77/0.96      (((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A) @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.77/0.96         = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['73', '74', '119', '150', '156'])).
% 0.77/0.96  thf('158', plain,
% 0.77/0.96      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 0.77/0.96          (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.77/0.96          = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['15', '157'])).
% 0.77/0.96  thf('159', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('160', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.77/0.96           = (k6_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.77/0.96  thf('161', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('162', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('163', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('164', plain,
% 0.77/0.96      (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.77/0.96         = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['158', '159', '160', '161', '162', '163'])).
% 0.77/0.96  thf('165', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf('166', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.77/0.96            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['164', '165'])).
% 0.77/0.96  thf('167', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['91', '115', '116', '117', '118'])).
% 0.77/0.96  thf('168', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('169', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.77/0.96            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.77/0.96  thf('170', plain,
% 0.77/0.96      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.77/0.96          = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 0.77/0.96             (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['14', '169'])).
% 0.77/0.96  thf('171', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('172', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf('173', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('174', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('175', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('176', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('177', plain,
% 0.77/0.96      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['175', '176'])).
% 0.77/0.96  thf('178', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('179', plain,
% 0.77/0.96      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['177', '178'])).
% 0.77/0.96  thf('180', plain,
% 0.77/0.96      (![X14 : $i]:
% 0.77/0.96         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.77/0.96          | ~ (v1_relat_1 @ X14))),
% 0.77/0.96      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.96  thf('181', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['50'])).
% 0.77/0.96  thf('182', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ X0 @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['180', '181'])).
% 0.77/0.96  thf('183', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('184', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ X0 @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1))),
% 0.77/0.96      inference('demod', [status(thm)], ['182', '183'])).
% 0.77/0.96  thf('185', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ X0 @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['184'])).
% 0.77/0.96  thf('186', plain,
% 0.77/0.96      (((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['179', '185'])).
% 0.77/0.96  thf('187', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('188', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('189', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.77/0.96  thf('190', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.77/0.96            = (k5_relat_1 @ X0 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['70', '71'])).
% 0.77/0.96  thf('191', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.77/0.96            = (k5_relat_1 @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['189', '190'])).
% 0.77/0.96  thf('192', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('193', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('194', plain,
% 0.77/0.96      (((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.77/0.96  thf('195', plain,
% 0.77/0.96      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.77/0.96  thf('196', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('197', plain,
% 0.77/0.96      ((((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96          = (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/0.96             (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))
% 0.77/0.96        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['195', '196'])).
% 0.77/0.96  thf('198', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.77/0.96  thf('199', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('200', plain,
% 0.77/0.96      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96         = (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/0.96            (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.77/0.96  thf('201', plain,
% 0.77/0.96      ((((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96          = (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/0.96             (k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['174', '200'])).
% 0.77/0.96  thf('202', plain,
% 0.77/0.96      (((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.77/0.96  thf('203', plain,
% 0.77/0.96      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.77/0.96  thf('204', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('205', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('206', plain,
% 0.77/0.96      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['201', '202', '203', '204', '205'])).
% 0.77/0.96  thf('207', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ X0 @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['184'])).
% 0.77/0.96  thf('208', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ 
% 0.77/0.96            (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['206', '207'])).
% 0.77/0.96  thf('209', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.77/0.96  thf('210', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ 
% 0.77/0.96           (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ 
% 0.77/0.96            (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['208', '209'])).
% 0.77/0.96  thf('211', plain,
% 0.77/0.96      (((v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['173', '210'])).
% 0.77/0.96  thf('212', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('213', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('214', plain,
% 0.77/0.96      ((v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['211', '212', '213'])).
% 0.77/0.96  thf('215', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.77/0.96            = (k5_relat_1 @ X0 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['70', '71'])).
% 0.77/0.96  thf('216', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96        | ((k5_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B) @ 
% 0.77/0.96            (k6_relat_1 @ 
% 0.77/0.96             (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))))
% 0.77/0.96            = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['214', '215'])).
% 0.77/0.96  thf('217', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('218', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.77/0.96  thf('219', plain,
% 0.77/0.96      (((k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['201', '202', '203', '204', '205'])).
% 0.77/0.96  thf('220', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('221', plain,
% 0.77/0.96      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.77/0.96  thf('222', plain,
% 0.77/0.96      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)) = (k1_relat_1 @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['220', '221'])).
% 0.77/0.96  thf('223', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('224', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('225', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('226', plain,
% 0.77/0.96      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 0.77/0.96  thf('227', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('228', plain,
% 0.77/0.96      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['226', '227'])).
% 0.77/0.96  thf('229', plain,
% 0.77/0.96      (((k5_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B) @ 
% 0.77/0.96         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96         = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['216', '217', '218', '219', '228'])).
% 0.77/0.96  thf('230', plain,
% 0.77/0.96      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 0.77/0.96          (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96          = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['172', '229'])).
% 0.77/0.96  thf('231', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.77/0.96      inference('demod', [status(thm)], ['0', '13'])).
% 0.77/0.96  thf('232', plain,
% 0.77/0.96      (![X19 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X19)
% 0.77/0.96          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.77/0.96              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.77/0.96          | ~ (v1_funct_1 @ X19)
% 0.77/0.96          | ~ (v1_relat_1 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.77/0.96  thf('233', plain,
% 0.77/0.96      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['177', '178'])).
% 0.77/0.96  thf('234', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf('235', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ sk_A @ X0)
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96               (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A))),
% 0.77/0.96      inference('sup+', [status(thm)], ['233', '234'])).
% 0.77/0.96  thf('236', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('237', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('238', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ sk_A @ X0)
% 0.77/0.96            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96               (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['235', '236', '237'])).
% 0.77/0.96  thf('239', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ 
% 0.77/0.96             (k5_relat_1 @ X0 @ 
% 0.77/0.96              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['184'])).
% 0.77/0.96  thf('240', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['238', '239'])).
% 0.77/0.96  thf('241', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('242', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['240', '241'])).
% 0.77/0.96  thf('243', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['63', '64'])).
% 0.77/0.96  thf('244', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X7)
% 0.77/0.96          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.77/0.96              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.77/0.96          | ~ (v1_relat_1 @ X9)
% 0.77/0.96          | ~ (v1_relat_1 @ X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.77/0.96  thf('245', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ sk_A @ X0)
% 0.77/0.96            = (k5_relat_1 @ sk_A @ 
% 0.77/0.96               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['243', '244'])).
% 0.77/0.96  thf('246', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('247', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('248', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k5_relat_1 @ sk_A @ X0)
% 0.77/0.96            = (k5_relat_1 @ sk_A @ 
% 0.77/0.96               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['245', '246', '247'])).
% 0.77/0.96  thf('249', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.77/0.96  thf('250', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['50'])).
% 0.77/0.96  thf('251', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X2)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['249', '250'])).
% 0.77/0.96  thf('252', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X2)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['251'])).
% 0.77/0.96  thf('253', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.77/0.96          | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['248', '252'])).
% 0.77/0.96  thf('254', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('255', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('256', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.77/0.96  thf('257', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['256'])).
% 0.77/0.96  thf('258', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0))))),
% 0.77/0.96      inference('clc', [status(thm)], ['242', '257'])).
% 0.77/0.96  thf('259', plain,
% 0.77/0.96      (((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_A)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_A)
% 0.77/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['232', '258'])).
% 0.77/0.96  thf('260', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('261', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('262', plain, ((v1_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('263', plain, ((v2_funct_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('264', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['91', '115', '116', '117', '118'])).
% 0.77/0.96  thf('265', plain,
% 0.77/0.96      ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['259', '260', '261', '262', '263', '264'])).
% 0.77/0.96  thf('266', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.77/0.96            = (k5_relat_1 @ X0 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['70', '71'])).
% 0.77/0.96  thf('267', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ((k5_relat_1 @ 
% 0.77/0.96            (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) @ 
% 0.77/0.96            (k6_relat_1 @ 
% 0.77/0.96             (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/0.96              (k2_relat_1 @ sk_B))))
% 0.77/0.96            = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['265', '266'])).
% 0.77/0.96  thf('268', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('269', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('270', plain,
% 0.77/0.96      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.77/0.96  thf('271', plain,
% 0.77/0.96      (((k5_relat_1 @ 
% 0.77/0.96         (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) @ 
% 0.77/0.96         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.77/0.96      inference('demod', [status(thm)], ['267', '268', '269', '270'])).
% 0.77/0.96  thf('272', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('273', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('274', plain, ((v1_relat_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('275', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96         = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['230', '231', '271', '272', '273', '274'])).
% 0.77/0.96  thf('276', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X5)
% 0.77/0.96          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.77/0.96             (k1_relat_1 @ X6))
% 0.77/0.96          | ~ (v1_relat_1 @ X6))),
% 0.77/0.96      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.77/0.96  thf('277', plain,
% 0.77/0.96      (((r1_tarski @ 
% 0.77/0.96         (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 0.77/0.96         (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['275', '276'])).
% 0.77/0.96  thf('278', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.77/0.96  thf('279', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('280', plain,
% 0.77/0.96      ((r1_tarski @ 
% 0.77/0.96        (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 0.77/0.96        (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['277', '278', '279'])).
% 0.77/0.96  thf('281', plain,
% 0.77/0.96      (((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 0.77/0.96         (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['171', '280'])).
% 0.77/0.96  thf('282', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('283', plain,
% 0.77/0.96      ((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 0.77/0.96        (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['281', '282'])).
% 0.77/0.96  thf('284', plain,
% 0.77/0.96      (![X12 : $i, X13 : $i]:
% 0.77/0.96         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.77/0.96          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.77/0.96          | ~ (v1_relat_1 @ X12))),
% 0.77/0.96      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.77/0.96  thf('285', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ((k5_relat_1 @ 
% 0.77/0.96            (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)
% 0.77/0.96            = (sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['283', '284'])).
% 0.77/0.96  thf('286', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('287', plain,
% 0.77/0.96      (((k5_relat_1 @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)
% 0.77/0.96         = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['285', '286'])).
% 0.77/0.96  thf('288', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.77/0.96            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.77/0.96            = (k5_relat_1 @ X0 @ X1))
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['70', '71'])).
% 0.77/0.96  thf('289', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ 
% 0.77/0.96             (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))
% 0.77/0.96        | ((k5_relat_1 @ 
% 0.77/0.96            (k5_relat_1 @ 
% 0.77/0.96             (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B) @ 
% 0.77/0.96            (k6_relat_1 @ 
% 0.77/0.96             (k9_relat_1 @ sk_B @ 
% 0.77/0.96              (k2_relat_1 @ 
% 0.77/0.96               (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))))))
% 0.77/0.96            = (k5_relat_1 @ 
% 0.77/0.96               (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['287', '288'])).
% 0.77/0.96  thf('290', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('291', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('292', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('293', plain,
% 0.77/0.96      (((k5_relat_1 @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)
% 0.77/0.96         = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['285', '286'])).
% 0.77/0.96  thf('294', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('295', plain,
% 0.77/0.96      (((k5_relat_1 @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)
% 0.77/0.96         = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['285', '286'])).
% 0.77/0.96  thf('296', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_B @ 
% 0.77/0.96         (k6_relat_1 @ 
% 0.77/0.96          (k9_relat_1 @ sk_B @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))))
% 0.77/0.96         = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['289', '290', '291', '292', '293', '294', '295'])).
% 0.77/0.96  thf('297', plain,
% 0.77/0.96      (((k5_relat_1 @ 
% 0.77/0.96         (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))) @ sk_B)
% 0.77/0.96         = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['285', '286'])).
% 0.77/0.96  thf('298', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X3)
% 0.77/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.77/0.96              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.77/0.96          | ~ (v1_relat_1 @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.77/0.96  thf('299', plain,
% 0.77/0.96      ((((k2_relat_1 @ sk_B)
% 0.77/0.96          = (k9_relat_1 @ sk_B @ 
% 0.77/0.96             (k2_relat_1 @ 
% 0.77/0.96              (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))))
% 0.77/0.96        | ~ (v1_relat_1 @ 
% 0.77/0.96             (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['297', '298'])).
% 0.77/0.96  thf('300', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.96  thf('301', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('302', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('303', plain,
% 0.77/0.96      (((k2_relat_1 @ sk_B)
% 0.77/0.96         = (k9_relat_1 @ sk_B @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['299', '300', '301', '302'])).
% 0.77/0.96  thf('304', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['296', '303'])).
% 0.77/0.96  thf('305', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X1)
% 0.77/0.96          | ~ (v1_relat_1 @ X0)
% 0.77/0.96          | ((k5_relat_1 @ X0 @ X1)
% 0.77/0.96              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.77/0.96                 (k5_relat_1 @ X0 @ X1))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['35'])).
% 0.77/0.96  thf('306', plain,
% 0.77/0.96      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_B)
% 0.77/0.96        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['304', '305'])).
% 0.77/0.96  thf('307', plain,
% 0.77/0.96      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['296', '303'])).
% 0.77/0.96  thf('308', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('309', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.96  thf('310', plain,
% 0.77/0.96      (((sk_B) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['306', '307', '308', '309'])).
% 0.77/0.96  thf('311', plain,
% 0.77/0.96      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.77/0.96         = (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['128', '129'])).
% 0.77/0.96  thf('312', plain, ((v1_relat_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('313', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['170', '310', '311', '312'])).
% 0.77/0.96  thf('314', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('315', plain, ($false),
% 0.77/0.96      inference('simplify_reflect-', [status(thm)], ['313', '314'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
