%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eF1TBB0oCo

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 134 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   21
%              Number of atoms          :  791 (1634 expanded)
%              Number of equality atoms :   68 ( 147 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('1',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('21',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('30',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k10_relat_1 @ X6 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('39',plain,
    ( ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['27','63'])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eF1TBB0oCo
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 62 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(t37_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.50  thf(t169_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 0.20/0.50          | ~ (v1_relat_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.50  thf(t167_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ (k10_relat_1 @ X2 @ X3) @ (k1_relat_1 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '6'])).
% 0.20/0.50  thf(dt_k4_relat_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(t47_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.50             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X8)
% 0.20/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X9)) = (k2_relat_1 @ X9))
% 0.20/0.50          | ~ (r1_tarski @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.20/0.50              = (k2_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.50          | ((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.20/0.50              = (k2_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.20/0.50              = (k2_relat_1 @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf(d9_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X10)
% 0.20/0.50          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.50          | ~ (v1_funct_1 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.50  thf(t59_funct_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) =>
% 0.20/0.50         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.20/0.50             ( k2_relat_1 @ A ) ) & 
% 0.20/0.50           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.20/0.50             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50          ( ( v2_funct_1 @ A ) =>
% 0.20/0.50            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.20/0.50                ( k2_relat_1 @ A ) ) & 
% 0.20/0.50              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.20/0.50                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          != (k2_relat_1 @ sk_A))
% 0.20/0.50        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50            != (k2_relat_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          != (k2_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.20/0.50           != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.50         | ~ (v2_funct_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.50  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.20/0.50          != (k2_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X10)
% 0.20/0.50          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.50          | ~ (v1_funct_1 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 0.20/0.50          | ~ (v1_relat_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.50            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.50              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X10)
% 0.20/0.50          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.50          | ~ (v1_funct_1 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.50  thf(t182_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.50             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X5)
% 0.20/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.20/0.50              = (k10_relat_1 @ X6 @ (k1_relat_1 @ X5)))
% 0.20/0.50          | ~ (v1_relat_1 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          != (k2_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['21'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((((k10_relat_1 @ (k2_funct_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.20/0.50           != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((((k10_relat_1 @ (k2_funct_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.20/0.50           != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.20/0.50           != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.50         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '41'])).
% 0.20/0.50  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.20/0.50           != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '46'])).
% 0.20/0.50  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.50         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.50         | ((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '49'])).
% 0.20/0.50  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.50         | ((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.50         | ((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '54'])).
% 0.20/0.50  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '57'])).
% 0.20/0.50  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50                = (k2_relat_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          = (k2_relat_1 @ sk_A)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (~
% 0.20/0.50       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          = (k2_relat_1 @ sk_A))) | 
% 0.20/0.50       ~
% 0.20/0.50       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          = (k2_relat_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['21'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (~
% 0.20/0.50       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.20/0.50          = (k2_relat_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.20/0.50         != (k2_relat_1 @ sk_A))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['27', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '64'])).
% 0.20/0.50  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
