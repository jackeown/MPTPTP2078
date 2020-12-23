%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ulYagZBBwu

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 116 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   21
%              Number of atoms          :  723 (1506 expanded)
%              Number of equality atoms :   57 ( 128 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('16',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('23',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('44',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ulYagZBBwu
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:11:21 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 60 iterations in 0.038s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.52  thf(t55_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ( v2_funct_1 @ A ) =>
% 0.23/0.52         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.23/0.52           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (![X10 : $i]:
% 0.23/0.52         (~ (v2_funct_1 @ X10)
% 0.23/0.52          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.23/0.52          | ~ (v1_funct_1 @ X10)
% 0.23/0.52          | ~ (v1_relat_1 @ X10))),
% 0.23/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.52  thf(dt_k2_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X9 : $i]:
% 0.23/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.23/0.52          | ~ (v1_funct_1 @ X9)
% 0.23/0.52          | ~ (v1_relat_1 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X9 : $i]:
% 0.23/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.23/0.52          | ~ (v1_funct_1 @ X9)
% 0.23/0.52          | ~ (v1_relat_1 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (![X10 : $i]:
% 0.23/0.52         (~ (v2_funct_1 @ X10)
% 0.23/0.52          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.23/0.52          | ~ (v1_funct_1 @ X10)
% 0.23/0.52          | ~ (v1_relat_1 @ X10))),
% 0.23/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.52  thf(t169_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X2 : $i]:
% 0.23/0.52         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.23/0.52          | ~ (v1_relat_1 @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.23/0.52  thf(t167_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ B ) =>
% 0.23/0.52       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.52      inference('sup+', [status(thm)], ['3', '7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0)
% 0.23/0.52          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '8'])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.52  thf(t47_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( v1_relat_1 @ B ) =>
% 0.23/0.52           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.23/0.52             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X6)
% 0.23/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 0.23/0.52          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 0.23/0.52          | ~ (v1_relat_1 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.23/0.52              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.23/0.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.23/0.52              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['1', '13'])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.23/0.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.23/0.52          | ~ (v2_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_funct_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.52  thf(t58_funct_1, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ( v2_funct_1 @ A ) =>
% 0.23/0.52         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.23/0.52             ( k1_relat_1 @ A ) ) & 
% 0.23/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.23/0.52             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52          ( ( v2_funct_1 @ A ) =>
% 0.23/0.52            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.23/0.52                ( k1_relat_1 @ A ) ) & 
% 0.23/0.52              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.23/0.52                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          != (k1_relat_1 @ sk_A))
% 0.23/0.52        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52            != (k1_relat_1 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          != (k1_relat_1 @ sk_A)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['16'])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X9 : $i]:
% 0.23/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.23/0.52          | ~ (v1_funct_1 @ X9)
% 0.23/0.52          | ~ (v1_relat_1 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X2 : $i]:
% 0.23/0.52         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.23/0.52          | ~ (v1_relat_1 @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.23/0.52  thf(t37_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.23/0.52         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X5 : $i]:
% 0.23/0.52         (((k2_relat_1 @ X5) = (k1_relat_1 @ (k4_relat_1 @ X5)))
% 0.23/0.52          | ~ (v1_relat_1 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.23/0.52  thf(d9_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X8 : $i]:
% 0.23/0.52         (~ (v2_funct_1 @ X8)
% 0.23/0.52          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.23/0.52          | ~ (v1_funct_1 @ X8)
% 0.23/0.52          | ~ (v1_relat_1 @ X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.23/0.52  thf(t182_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( v1_relat_1 @ B ) =>
% 0.23/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.23/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X3 : $i, X4 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X3)
% 0.23/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.23/0.52              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.23/0.52          | ~ (v1_relat_1 @ X4))),
% 0.23/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          != (k1_relat_1 @ sk_A)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['16'])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.23/0.52           != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.52  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.23/0.52           != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.23/0.52           != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52         | ~ (v1_funct_1 @ sk_A)
% 0.23/0.52         | ~ (v2_funct_1 @ sk_A)
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '26'])).
% 0.23/0.52  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('30', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.23/0.52           != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k2_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['20', '31'])).
% 0.23/0.52  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (((((k10_relat_1 @ sk_A @ (k2_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['19', '34'])).
% 0.23/0.52  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.23/0.52  thf('39', plain,
% 0.23/0.52      (((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52                = (k1_relat_1 @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['18', '38'])).
% 0.23/0.52  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('42', plain,
% 0.23/0.52      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          = (k1_relat_1 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      (~
% 0.23/0.52       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          = (k1_relat_1 @ sk_A))) | 
% 0.23/0.52       ~
% 0.23/0.52       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          = (k1_relat_1 @ sk_A)))),
% 0.23/0.52      inference('split', [status(esa)], ['16'])).
% 0.23/0.52  thf('44', plain,
% 0.23/0.52      (~
% 0.23/0.52       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52          = (k1_relat_1 @ sk_A)))),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.23/0.52  thf('45', plain,
% 0.23/0.52      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.23/0.52         != (k1_relat_1 @ sk_A))),
% 0.23/0.52      inference('simpl_trail', [status(thm)], ['17', '44'])).
% 0.23/0.52  thf('46', plain,
% 0.23/0.52      ((((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['15', '45'])).
% 0.23/0.52  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('49', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      (((k2_relat_1 @ (k2_funct_1 @ sk_A)) != (k1_relat_1 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.23/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['0', '50'])).
% 0.23/0.52  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('54', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('55', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.23/0.52  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
