%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4tA7MTNkkO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  69 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   21
%              Number of atoms          :  636 ( 730 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X8 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t62_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_1])).

thf('32',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34','35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4tA7MTNkkO
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 26 iterations in 0.024s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(dt_k2_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X3 : $i]:
% 0.20/0.45         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.20/0.45          | ~ (v1_funct_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X3 : $i]:
% 0.20/0.45         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.20/0.45          | ~ (v1_funct_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.45  thf(t61_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ( v2_funct_1 @ A ) =>
% 0.20/0.45         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.20/0.45             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.45           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.20/0.45             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X11 : $i]:
% 0.20/0.45         (~ (v2_funct_1 @ X11)
% 0.20/0.45          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.20/0.45              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.20/0.45          | ~ (v1_funct_1 @ X11)
% 0.20/0.45          | ~ (v1_relat_1 @ X11))),
% 0.20/0.45      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X3 : $i]:
% 0.20/0.45         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.20/0.45          | ~ (v1_funct_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X3 : $i]:
% 0.20/0.45         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.20/0.45          | ~ (v1_funct_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X3 : $i]:
% 0.20/0.45         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.20/0.45          | ~ (v1_funct_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.45  thf(t55_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ( v2_funct_1 @ A ) =>
% 0.20/0.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X10 : $i]:
% 0.20/0.45         (~ (v2_funct_1 @ X10)
% 0.20/0.45          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.20/0.45          | ~ (v1_funct_1 @ X10)
% 0.20/0.45          | ~ (v1_relat_1 @ X10))),
% 0.20/0.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.45  thf(t169_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.45            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.45              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.45            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.45  thf(t182_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( v1_relat_1 @ B ) =>
% 0.20/0.45           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.45             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.20/0.45              = (k10_relat_1 @ X2 @ (k1_relat_1 @ X1)))
% 0.20/0.45          | ~ (v1_relat_1 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.45  thf(t27_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.45           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.20/0.45             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X6)
% 0.20/0.45          | ~ (v1_funct_1 @ X6)
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X7))
% 0.20/0.45          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X7)) != (k1_relat_1 @ X6))
% 0.20/0.45          | ~ (v1_funct_1 @ X7)
% 0.20/0.45          | ~ (v1_relat_1 @ X7))),
% 0.20/0.45      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) != (k1_relat_1 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (v1_funct_1 @ X1)
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) != (k1_relat_1 @ X1)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['4', '16'])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '18'])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.45  thf(t47_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.45           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.20/0.45               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.45             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X8)
% 0.20/0.45          | ~ (v1_funct_1 @ X8)
% 0.20/0.45          | (v2_funct_1 @ X8)
% 0.20/0.45          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X9))
% 0.20/0.45          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 0.20/0.45          | ~ (v1_funct_1 @ X9)
% 0.20/0.45          | ~ (v1_relat_1 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '23'])).
% 0.20/0.45  thf(fc4_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.45  thf('25', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '27'])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '29'])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.45  thf(t62_funct_1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.45          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.20/0.45  thf('32', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.45  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('36', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('37', plain, ($false),
% 0.20/0.45      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
