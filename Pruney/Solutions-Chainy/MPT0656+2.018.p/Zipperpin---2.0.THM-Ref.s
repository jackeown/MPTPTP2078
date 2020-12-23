%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SPLV8RK95R

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:39 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 227 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   24
%              Number of atoms          : 1039 (3134 expanded)
%              Number of equality atoms :   75 ( 300 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X15 ) @ X15 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
       != ( k6_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X4 ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','35'])).

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
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('53',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60'])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X4 ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','81'])).

thf('83',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X4 ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','87','88'])).

thf('90',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SPLV8RK95R
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.05/2.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.05/2.24  % Solved by: fo/fo7.sh
% 2.05/2.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.24  % done 902 iterations in 1.784s
% 2.05/2.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.05/2.24  % SZS output start Refutation
% 2.05/2.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.05/2.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.05/2.24  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.05/2.24  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.05/2.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.05/2.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.05/2.24  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.05/2.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.24  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.05/2.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.05/2.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.05/2.24  thf(t63_funct_1, conjecture,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24       ( ![B:$i]:
% 2.05/2.24         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.05/2.24           ( ( ( v2_funct_1 @ A ) & 
% 2.05/2.24               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.05/2.24               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.05/2.24             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.05/2.24  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.24    (~( ![A:$i]:
% 2.05/2.24        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24          ( ![B:$i]:
% 2.05/2.24            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.05/2.24              ( ( ( v2_funct_1 @ A ) & 
% 2.05/2.24                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.05/2.24                  ( ( k5_relat_1 @ A @ B ) =
% 2.05/2.24                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.05/2.24                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 2.05/2.24    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 2.05/2.24  thf('0', plain,
% 2.05/2.24      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf(dt_k2_funct_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.05/2.24         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.05/2.24  thf('1', plain,
% 2.05/2.24      (![X6 : $i]:
% 2.05/2.24         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.05/2.24          | ~ (v1_funct_1 @ X6)
% 2.05/2.24          | ~ (v1_relat_1 @ X6))),
% 2.05/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.05/2.24  thf(t55_funct_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24       ( ( v2_funct_1 @ A ) =>
% 2.05/2.24         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.05/2.24           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.05/2.24  thf('2', plain,
% 2.05/2.24      (![X14 : $i]:
% 2.05/2.24         (~ (v2_funct_1 @ X14)
% 2.05/2.24          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 2.05/2.24          | ~ (v1_funct_1 @ X14)
% 2.05/2.24          | ~ (v1_relat_1 @ X14))),
% 2.05/2.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.05/2.24  thf(t80_relat_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( v1_relat_1 @ A ) =>
% 2.05/2.24       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.05/2.24  thf('3', plain,
% 2.05/2.24      (![X5 : $i]:
% 2.05/2.24         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 2.05/2.24          | ~ (v1_relat_1 @ X5))),
% 2.05/2.24      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.05/2.24  thf('4', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.05/2.24            = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.05/2.24      inference('sup+', [status(thm)], ['2', '3'])).
% 2.05/2.24  thf('5', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.05/2.24              = (k2_funct_1 @ X0)))),
% 2.05/2.24      inference('sup-', [status(thm)], ['1', '4'])).
% 2.05/2.24  thf('6', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.05/2.24            = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('simplify', [status(thm)], ['5'])).
% 2.05/2.24  thf('7', plain,
% 2.05/2.24      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 2.05/2.24          = (k2_funct_1 @ sk_A))
% 2.05/2.24        | ~ (v1_relat_1 @ sk_A)
% 2.05/2.24        | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24        | ~ (v2_funct_1 @ sk_A))),
% 2.05/2.24      inference('sup+', [status(thm)], ['0', '6'])).
% 2.05/2.24  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('10', plain, ((v2_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('11', plain,
% 2.05/2.24      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 2.05/2.24         = (k2_funct_1 @ sk_A))),
% 2.05/2.24      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.05/2.24  thf('12', plain,
% 2.05/2.24      (![X6 : $i]:
% 2.05/2.24         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.05/2.24          | ~ (v1_funct_1 @ X6)
% 2.05/2.24          | ~ (v1_relat_1 @ X6))),
% 2.05/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.05/2.24  thf(t61_funct_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24       ( ( v2_funct_1 @ A ) =>
% 2.05/2.24         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.05/2.24             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.05/2.24           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.05/2.24             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.05/2.24  thf('13', plain,
% 2.05/2.24      (![X15 : $i]:
% 2.05/2.24         (~ (v2_funct_1 @ X15)
% 2.05/2.24          | ((k5_relat_1 @ (k2_funct_1 @ X15) @ X15)
% 2.05/2.24              = (k6_relat_1 @ (k2_relat_1 @ X15)))
% 2.05/2.24          | ~ (v1_funct_1 @ X15)
% 2.05/2.24          | ~ (v1_relat_1 @ X15))),
% 2.05/2.24      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.05/2.24  thf('14', plain,
% 2.05/2.24      (![X6 : $i]:
% 2.05/2.24         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.05/2.24          | ~ (v1_funct_1 @ X6)
% 2.05/2.24          | ~ (v1_relat_1 @ X6))),
% 2.05/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.05/2.24  thf('15', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('16', plain,
% 2.05/2.24      (![X6 : $i]:
% 2.05/2.24         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.05/2.24          | ~ (v1_funct_1 @ X6)
% 2.05/2.24          | ~ (v1_relat_1 @ X6))),
% 2.05/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.05/2.24  thf('17', plain,
% 2.05/2.24      (![X5 : $i]:
% 2.05/2.24         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 2.05/2.24          | ~ (v1_relat_1 @ X5))),
% 2.05/2.24      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.05/2.24  thf(t27_funct_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.05/2.24       ( ![B:$i]:
% 2.05/2.24         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.05/2.24           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 2.05/2.24             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 2.05/2.24  thf('18', plain,
% 2.05/2.24      (![X9 : $i, X10 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X9)
% 2.05/2.24          | ~ (v1_funct_1 @ X9)
% 2.05/2.24          | (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X10))
% 2.05/2.24          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k1_relat_1 @ X9))
% 2.05/2.24          | ~ (v1_funct_1 @ X10)
% 2.05/2.24          | ~ (v1_relat_1 @ X10))),
% 2.05/2.24      inference('cnf', [status(esa)], [t27_funct_1])).
% 2.05/2.24  thf('19', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.05/2.24          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.05/2.24          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.05/2.24             (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('sup-', [status(thm)], ['17', '18'])).
% 2.05/2.24  thf(fc3_funct_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.05/2.24       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.05/2.24  thf('20', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf('21', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf(t34_funct_1, axiom,
% 2.05/2.24    (![A:$i,B:$i]:
% 2.05/2.24     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.05/2.24       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 2.05/2.24         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 2.05/2.24           ( ![C:$i]:
% 2.05/2.24             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 2.05/2.24  thf('22', plain,
% 2.05/2.24      (![X11 : $i, X12 : $i]:
% 2.05/2.24         (((X12) != (k6_relat_1 @ X11))
% 2.05/2.24          | ((k1_relat_1 @ X12) = (X11))
% 2.05/2.24          | ~ (v1_funct_1 @ X12)
% 2.05/2.24          | ~ (v1_relat_1 @ X12))),
% 2.05/2.24      inference('cnf', [status(esa)], [t34_funct_1])).
% 2.05/2.24  thf('23', plain,
% 2.05/2.24      (![X11 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ (k6_relat_1 @ X11))
% 2.05/2.24          | ~ (v1_funct_1 @ (k6_relat_1 @ X11))
% 2.05/2.24          | ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11)))),
% 2.05/2.24      inference('simplify', [status(thm)], ['22'])).
% 2.05/2.24  thf('24', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf('25', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf('26', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.05/2.24      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.05/2.24  thf('27', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('demod', [status(thm)], ['19', '20', '21', '26'])).
% 2.05/2.24  thf('28', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_funct_1 @ X0)
% 2.05/2.24          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('simplify', [status(thm)], ['27'])).
% 2.05/2.24  thf('29', plain,
% 2.05/2.24      (![X14 : $i]:
% 2.05/2.24         (~ (v2_funct_1 @ X14)
% 2.05/2.24          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 2.05/2.24          | ~ (v1_funct_1 @ X14)
% 2.05/2.24          | ~ (v1_relat_1 @ X14))),
% 2.05/2.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.05/2.24  thf(t77_relat_1, axiom,
% 2.05/2.24    (![A:$i,B:$i]:
% 2.05/2.24     ( ( v1_relat_1 @ B ) =>
% 2.05/2.24       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.05/2.24         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.05/2.24  thf('30', plain,
% 2.05/2.24      (![X3 : $i, X4 : $i]:
% 2.05/2.24         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X4) @ X3) = (X3))
% 2.05/2.24          | ~ (v1_relat_1 @ X3))),
% 2.05/2.24      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.05/2.24  thf('31', plain,
% 2.05/2.24      (![X0 : $i, X1 : $i]:
% 2.05/2.24         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k2_funct_1 @ X0))
% 2.05/2.24              = (k2_funct_1 @ X0)))),
% 2.05/2.24      inference('sup-', [status(thm)], ['29', '30'])).
% 2.05/2.24  thf('32', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.05/2.24              = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('sup-', [status(thm)], ['28', '31'])).
% 2.05/2.24  thf('33', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v2_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.05/2.24              = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('simplify', [status(thm)], ['32'])).
% 2.05/2.24  thf('34', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.05/2.24              = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v2_funct_1 @ X0))),
% 2.05/2.24      inference('sup-', [status(thm)], ['16', '33'])).
% 2.05/2.24  thf('35', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v2_funct_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.05/2.24              = (k2_funct_1 @ X0))
% 2.05/2.24          | ~ (v1_funct_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('simplify', [status(thm)], ['34'])).
% 2.05/2.24  thf('36', plain,
% 2.05/2.24      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 2.05/2.24          = (k2_funct_1 @ sk_A))
% 2.05/2.24        | ~ (v1_relat_1 @ sk_A)
% 2.05/2.24        | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24        | ~ (v2_funct_1 @ sk_A))),
% 2.05/2.24      inference('sup+', [status(thm)], ['15', '35'])).
% 2.05/2.24  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('39', plain, ((v2_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('40', plain,
% 2.05/2.24      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 2.05/2.24         = (k2_funct_1 @ sk_A))),
% 2.05/2.24      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 2.05/2.24  thf(t55_relat_1, axiom,
% 2.05/2.24    (![A:$i]:
% 2.05/2.24     ( ( v1_relat_1 @ A ) =>
% 2.05/2.24       ( ![B:$i]:
% 2.05/2.24         ( ( v1_relat_1 @ B ) =>
% 2.05/2.24           ( ![C:$i]:
% 2.05/2.24             ( ( v1_relat_1 @ C ) =>
% 2.05/2.24               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.05/2.24                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.05/2.24  thf('41', plain,
% 2.05/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 2.05/2.24              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.05/2.24          | ~ (v1_relat_1 @ X2)
% 2.05/2.24          | ~ (v1_relat_1 @ X1))),
% 2.05/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.05/2.24  thf('42', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.05/2.24            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24               (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 2.05/2.24          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 2.05/2.24      inference('sup+', [status(thm)], ['40', '41'])).
% 2.05/2.24  thf('43', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf('44', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.05/2.24            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24               (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 2.05/2.24      inference('demod', [status(thm)], ['42', '43'])).
% 2.05/2.24  thf('45', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ sk_A)
% 2.05/2.24          | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.05/2.24              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24                 (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0))))),
% 2.05/2.24      inference('sup-', [status(thm)], ['14', '44'])).
% 2.05/2.24  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('47', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('48', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.05/2.24              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24                 (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0))))),
% 2.05/2.24      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.05/2.24  thf('49', plain,
% 2.05/2.24      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 2.05/2.24          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24             (k6_relat_1 @ (k2_relat_1 @ sk_A))))
% 2.05/2.24        | ~ (v1_relat_1 @ sk_A)
% 2.05/2.24        | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24        | ~ (v2_funct_1 @ sk_A)
% 2.05/2.24        | ~ (v1_relat_1 @ sk_A))),
% 2.05/2.24      inference('sup+', [status(thm)], ['13', '48'])).
% 2.05/2.24  thf('50', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('51', plain,
% 2.05/2.24      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('52', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.05/2.24      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.05/2.24  thf('53', plain,
% 2.05/2.24      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 2.05/2.24      inference('sup+', [status(thm)], ['51', '52'])).
% 2.05/2.24  thf('54', plain,
% 2.05/2.24      (![X9 : $i, X10 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X9)
% 2.05/2.24          | ~ (v1_funct_1 @ X9)
% 2.05/2.24          | (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X10))
% 2.05/2.24          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k1_relat_1 @ X9))
% 2.05/2.24          | ~ (v1_funct_1 @ X10)
% 2.05/2.24          | ~ (v1_relat_1 @ X10))),
% 2.05/2.24      inference('cnf', [status(esa)], [t27_funct_1])).
% 2.05/2.24  thf('55', plain,
% 2.05/2.24      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 2.05/2.24        | ~ (v1_relat_1 @ sk_B)
% 2.05/2.24        | ~ (v1_funct_1 @ sk_B)
% 2.05/2.24        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 2.05/2.24        | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24        | ~ (v1_relat_1 @ sk_A))),
% 2.05/2.24      inference('sup-', [status(thm)], ['53', '54'])).
% 2.05/2.24  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('58', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('59', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('61', plain,
% 2.05/2.24      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 2.05/2.24        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 2.05/2.24      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '60'])).
% 2.05/2.24  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 2.05/2.24      inference('simplify', [status(thm)], ['61'])).
% 2.05/2.24  thf('63', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.05/2.24      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.05/2.24  thf('64', plain,
% 2.05/2.24      (![X3 : $i, X4 : $i]:
% 2.05/2.24         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X4) @ X3) = (X3))
% 2.05/2.24          | ~ (v1_relat_1 @ X3))),
% 2.05/2.24      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.05/2.24  thf('65', plain,
% 2.05/2.24      (![X0 : $i, X1 : $i]:
% 2.05/2.24         (~ (r1_tarski @ X0 @ X1)
% 2.05/2.24          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.05/2.24              = (k6_relat_1 @ X0)))),
% 2.05/2.24      inference('sup-', [status(thm)], ['63', '64'])).
% 2.05/2.24  thf('66', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 2.05/2.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.05/2.24  thf('67', plain,
% 2.05/2.24      (![X0 : $i, X1 : $i]:
% 2.05/2.24         (~ (r1_tarski @ X0 @ X1)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.05/2.24              = (k6_relat_1 @ X0)))),
% 2.05/2.24      inference('demod', [status(thm)], ['65', '66'])).
% 2.05/2.24  thf('68', plain,
% 2.05/2.24      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.05/2.24         (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.05/2.24         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 2.05/2.24      inference('sup-', [status(thm)], ['62', '67'])).
% 2.05/2.24  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('70', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('71', plain, ((v2_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('73', plain,
% 2.05/2.24      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 2.05/2.24         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 2.05/2.24      inference('demod', [status(thm)],
% 2.05/2.24                ['49', '50', '68', '69', '70', '71', '72'])).
% 2.05/2.24  thf('74', plain,
% 2.05/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 2.05/2.24              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.05/2.24          | ~ (v1_relat_1 @ X2)
% 2.05/2.24          | ~ (v1_relat_1 @ X1))),
% 2.05/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.05/2.24  thf('75', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.05/2.24            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ~ (v1_relat_1 @ sk_A))),
% 2.05/2.24      inference('sup+', [status(thm)], ['73', '74'])).
% 2.05/2.24  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('77', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.05/2.24            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 2.05/2.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.05/2.24          | ~ (v1_relat_1 @ X0))),
% 2.05/2.24      inference('demod', [status(thm)], ['75', '76'])).
% 2.05/2.24  thf('78', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ sk_A)
% 2.05/2.24          | ~ (v1_funct_1 @ sk_A)
% 2.05/2.24          | ~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.05/2.24              = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 2.05/2.24      inference('sup-', [status(thm)], ['12', '77'])).
% 2.05/2.24  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('80', plain, ((v1_funct_1 @ sk_A)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('81', plain,
% 2.05/2.24      (![X0 : $i]:
% 2.05/2.24         (~ (v1_relat_1 @ X0)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.05/2.24              = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 2.05/2.24      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.05/2.24  thf('82', plain,
% 2.05/2.24      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 2.05/2.24          = (k2_funct_1 @ sk_A))
% 2.05/2.24        | ~ (v1_relat_1 @ sk_B))),
% 2.05/2.24      inference('sup+', [status(thm)], ['11', '81'])).
% 2.05/2.24  thf('83', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 2.05/2.24      inference('simplify', [status(thm)], ['61'])).
% 2.05/2.24  thf('84', plain,
% 2.05/2.24      (![X3 : $i, X4 : $i]:
% 2.05/2.24         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 2.05/2.24          | ((k5_relat_1 @ (k6_relat_1 @ X4) @ X3) = (X3))
% 2.05/2.24          | ~ (v1_relat_1 @ X3))),
% 2.05/2.24      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.05/2.24  thf('85', plain,
% 2.05/2.24      ((~ (v1_relat_1 @ sk_B)
% 2.05/2.24        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B)))),
% 2.05/2.24      inference('sup-', [status(thm)], ['83', '84'])).
% 2.05/2.24  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('87', plain,
% 2.05/2.24      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B))),
% 2.05/2.24      inference('demod', [status(thm)], ['85', '86'])).
% 2.05/2.24  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('89', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 2.05/2.24      inference('demod', [status(thm)], ['82', '87', '88'])).
% 2.05/2.24  thf('90', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 2.05/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.24  thf('91', plain, ($false),
% 2.05/2.24      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 2.05/2.24  
% 2.05/2.24  % SZS output end Refutation
% 2.05/2.24  
% 2.05/2.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
