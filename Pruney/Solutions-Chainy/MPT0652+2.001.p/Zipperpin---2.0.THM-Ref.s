%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jekmg93QY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 124 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   23
%              Number of atoms          :  723 (1558 expanded)
%              Number of equality atoms :   68 ( 146 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

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

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('19',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('25',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k9_relat_1 @ X7 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
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
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('52',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','52'])).

thf('54',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6jekmg93QY
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 152 iterations in 0.107s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(t37_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.57         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X9 : $i]:
% 0.21/0.57         (((k2_relat_1 @ X9) = (k1_relat_1 @ (k4_relat_1 @ X9)))
% 0.21/0.57          | ~ (v1_relat_1 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X9 : $i]:
% 0.21/0.57         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 0.21/0.57          | ~ (v1_relat_1 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.57  thf(t46_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( v1_relat_1 @ B ) =>
% 0.21/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X10)
% 0.21/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) = (k1_relat_1 @ X11))
% 0.21/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.21/0.57          | ~ (v1_relat_1 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.57          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.21/0.57              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.57              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.57          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.57              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.57  thf(dt_k4_relat_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.57              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.21/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(d9_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X13 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X13)
% 0.21/0.57          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X13)
% 0.21/0.57          | ~ (v1_relat_1 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf(t59_funct_1, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ A ) =>
% 0.21/0.57         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.57             ( k2_relat_1 @ A ) ) & 
% 0.21/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.57             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57          ( ( v2_funct_1 @ A ) =>
% 0.21/0.57            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.57                ( k2_relat_1 @ A ) ) & 
% 0.21/0.57              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.57                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          != (k2_relat_1 @ sk_A))
% 0.21/0.57        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57            != (k2_relat_1 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          != (k2_relat_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.57           != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.57  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('16', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.57          != (k2_relat_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X13 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X13)
% 0.21/0.57          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X13)
% 0.21/0.57          | ~ (v1_relat_1 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf(t98_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X12 : $i]:
% 0.21/0.57         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.57  thf(t148_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ B ) =>
% 0.21/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]:
% 0.21/0.57         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.57          | ~ (v1_relat_1 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X9 : $i]:
% 0.21/0.57         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 0.21/0.57          | ~ (v1_relat_1 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X13 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X13)
% 0.21/0.57          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X13)
% 0.21/0.57          | ~ (v1_relat_1 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf(t160_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( v1_relat_1 @ B ) =>
% 0.21/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.57             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X7)
% 0.21/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.21/0.57              = (k9_relat_1 @ X7 @ (k2_relat_1 @ X8)))
% 0.21/0.57          | ~ (v1_relat_1 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          != (k2_relat_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.57           != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.57           != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.57           != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_A)
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.57  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('34', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.57           != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '35'])).
% 0.21/0.57  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '38'])).
% 0.21/0.57  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '42'])).
% 0.21/0.57  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_A))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57                = (k2_relat_1 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '47'])).
% 0.21/0.57  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          = (k2_relat_1 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          = (k2_relat_1 @ sk_A))) | 
% 0.21/0.57       ~
% 0.21/0.57       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          = (k2_relat_1 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.57          = (k2_relat_1 @ sk_A)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.57         != (k2_relat_1 @ sk_A))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['17', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '53'])).
% 0.21/0.57  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '56'])).
% 0.21/0.57  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
