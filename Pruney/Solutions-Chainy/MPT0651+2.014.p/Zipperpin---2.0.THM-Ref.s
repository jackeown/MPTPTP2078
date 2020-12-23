%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nA2ygit1ct

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:24 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 138 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   30
%              Number of atoms          :  885 (1610 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

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

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('23',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('27',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('28',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('51',plain,
    ( ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('63',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','63'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nA2ygit1ct
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 146 iterations in 0.119s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(fc24_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.38/0.57       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.38/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('0', plain, (![X12 : $i]: (v4_relat_1 @ (k6_relat_1 @ X12) @ X12)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.38/0.57  thf(d18_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v4_relat_1 @ X0 @ X1)
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.38/0.57  thf(t71_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.57  thf('4', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.38/0.57  thf(t37_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.38/0.57         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X3 : $i]:
% 0.38/0.57         (((k2_relat_1 @ X3) = (k1_relat_1 @ (k4_relat_1 @ X3)))
% 0.38/0.57          | ~ (v1_relat_1 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.57  thf(t46_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( v1_relat_1 @ B ) =>
% 0.38/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X4)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4)) = (k1_relat_1 @ X5))
% 0.38/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X5) @ (k1_relat_1 @ X4))
% 0.38/0.57          | ~ (v1_relat_1 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X1)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.38/0.57              = (k1_relat_1 @ X1))
% 0.38/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.38/0.57              = (k1_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.38/0.57              = (k1_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.57  thf(dt_k4_relat_1, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.38/0.57            = (k1_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf(d9_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X10)
% 0.38/0.57          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.38/0.57          | ~ (v1_funct_1 @ X10)
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf(t58_funct_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) =>
% 0.38/0.57         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.38/0.57             ( k1_relat_1 @ A ) ) & 
% 0.38/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.38/0.57             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57          ( ( v2_funct_1 @ A ) =>
% 0.38/0.57            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.38/0.57                ( k1_relat_1 @ A ) ) & 
% 0.38/0.57              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.38/0.57                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57          != (k1_relat_1 @ sk_A))
% 0.38/0.57        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57            != (k1_relat_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57          != (k1_relat_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57                = (k1_relat_1 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.38/0.57           != (k1_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.57         | ~ (v2_funct_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57                = (k1_relat_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.38/0.57  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('19', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.38/0.57          != (k1_relat_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.57                = (k1_relat_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.38/0.57  thf(t55_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) =>
% 0.38/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X14)
% 0.38/0.57          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X10)
% 0.38/0.57          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.38/0.57          | ~ (v1_funct_1 @ X10)
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X10)
% 0.38/0.57          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.38/0.57          | ~ (v1_funct_1 @ X10)
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X10)
% 0.38/0.57          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.38/0.57          | ~ (v1_funct_1 @ X10)
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X14)
% 0.38/0.57          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.57          | (v4_relat_1 @ X0 @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['28', '31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['27', '32'])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v4_relat_1 @ X0 @ X1)
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.57  thf(t47_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( v1_relat_1 @ B ) =>
% 0.38/0.57           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.38/0.57             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X6)
% 0.38/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 0.38/0.57          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 0.38/0.57          | ~ (v1_relat_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.57              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.57            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v2_funct_1 @ X0)
% 0.38/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.58              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '45'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.58            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.38/0.58          | ~ (v2_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v2_funct_1 @ X0)
% 0.38/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.58              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '47'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.38/0.58            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.38/0.58          | ~ (v2_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58          != (k1_relat_1 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58                = (k1_relat_1 @ sk_A))))),
% 0.38/0.58      inference('split', [status(esa)], ['14'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.38/0.58         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58         | ~ (v2_funct_1 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58                = (k1_relat_1 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.58  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('54', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58                = (k1_relat_1 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.38/0.58         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58         | ~ (v2_funct_1 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58                = (k1_relat_1 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '55'])).
% 0.38/0.58  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('59', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58                = (k1_relat_1 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58          = (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (~
% 0.38/0.58       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58          = (k1_relat_1 @ sk_A))) | 
% 0.38/0.58       ~
% 0.38/0.58       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58          = (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['14'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (~
% 0.38/0.58       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.38/0.58          = (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.38/0.58         != (k1_relat_1 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['20', '63'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '64'])).
% 0.38/0.58  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('67', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
