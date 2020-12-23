%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SrQDzAXj76

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 139 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   29
%              Number of atoms          :  749 (1751 expanded)
%              Number of equality atoms :   70 ( 162 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('5',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('9',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('10',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( ( k7_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('45',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','49'])).

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
    ( ( ( k10_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SrQDzAXj76
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 44 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(dt_k4_relat_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf(d9_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X10)
% 0.20/0.48          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf(t169_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.20/0.48          | ~ (v1_relat_1 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.48  thf(t55_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) =>
% 0.20/0.48         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.48           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X11)
% 0.20/0.48          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.48          | ~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.48  thf(t182_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X6)
% 0.20/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.20/0.48              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.48  thf(t58_funct_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) =>
% 0.20/0.48         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48             ( k1_relat_1 @ A ) ) & 
% 0.20/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48          ( ( v2_funct_1 @ A ) =>
% 0.20/0.48            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48                ( k1_relat_1 @ A ) ) & 
% 0.20/0.48              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A))
% 0.20/0.48        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48            != (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf(t37_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X8) = (k2_relat_1 @ (k4_relat_1 @ X8)))
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X10)
% 0.20/0.48          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X8) = (k1_relat_1 @ (k4_relat_1 @ X8)))
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf(t98_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (X9)) | ~ (v1_relat_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X2)) = (k9_relat_1 @ X1 @ X2))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.49            = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.49              = (k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X10 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X10)
% 0.20/0.49          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.49          | ~ (v1_funct_1 @ X10)
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.49  thf(t160_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.49             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X3)
% 0.20/0.49          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.20/0.49              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 0.20/0.49          | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          != (k1_relat_1 @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.49           != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.49           != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.49           != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.49           != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '28'])).
% 0.20/0.49  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.49         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '31'])).
% 0.20/0.49  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.49         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.49         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '39'])).
% 0.20/0.49  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49                = (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          = (k1_relat_1 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          = (k1_relat_1 @ sk_A))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          = (k1_relat_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          = (k1_relat_1 @ sk_A)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.49         != (k1_relat_1 @ sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.20/0.49          != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ (k2_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_A)
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '49'])).
% 0.20/0.49  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ (k2_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '54'])).
% 0.20/0.49  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '58'])).
% 0.20/0.49  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain, (~ (v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.49  thf('64', plain, (~ (v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '63'])).
% 0.20/0.49  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('66', plain, ($false), inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
