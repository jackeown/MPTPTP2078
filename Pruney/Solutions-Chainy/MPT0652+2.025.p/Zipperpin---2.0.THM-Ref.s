%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VChqI7ZKv6

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:30 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 133 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   25
%              Number of atoms          :  752 (1680 expanded)
%              Number of equality atoms :   72 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('9',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('20',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('29',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

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
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
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
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('53',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['18','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VChqI7ZKv6
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 172 iterations in 0.086s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(t37_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.37/0.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (![X9 : $i]:
% 0.37/0.54         (((k2_relat_1 @ X9) = (k1_relat_1 @ (k4_relat_1 @ X9)))
% 0.37/0.54          | ~ (v1_relat_1 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.37/0.54  thf(dt_k4_relat_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X9 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 0.37/0.54          | ~ (v1_relat_1 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.37/0.54  thf(t169_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X6 : $i]:
% 0.37/0.54         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.37/0.54          | ~ (v1_relat_1 @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.54            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.54              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.37/0.54      inference('clc', [status(thm)], ['4', '5'])).
% 0.37/0.54  thf(t182_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( v1_relat_1 @ B ) =>
% 0.37/0.54           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.37/0.54             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X7 : $i, X8 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X7)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.37/0.54              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 0.37/0.54          | ~ (v1_relat_1 @ X8))),
% 0.37/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.37/0.54  thf(d9_funct_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X11 : $i]:
% 0.37/0.54         (~ (v2_funct_1 @ X11)
% 0.37/0.54          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.37/0.54          | ~ (v1_funct_1 @ X11)
% 0.37/0.54          | ~ (v1_relat_1 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.54  thf(t59_funct_1, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54       ( ( v2_funct_1 @ A ) =>
% 0.37/0.54         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.37/0.54             ( k2_relat_1 @ A ) ) & 
% 0.37/0.54           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.37/0.54             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.54          ( ( v2_funct_1 @ A ) =>
% 0.37/0.54            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.37/0.54                ( k2_relat_1 @ A ) ) & 
% 0.37/0.54              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.37/0.54                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          != (k2_relat_1 @ sk_A))
% 0.37/0.54        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54            != (k2_relat_1 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          != (k2_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('split', [status(esa)], ['9'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.37/0.54         | ~ (v2_funct_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['8', '10'])).
% 0.37/0.54  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('14', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      ((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.37/0.54          != (k2_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['7', '15'])).
% 0.37/0.54  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X11 : $i]:
% 0.37/0.54         (~ (v2_funct_1 @ X11)
% 0.37/0.54          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.37/0.54          | ~ (v1_funct_1 @ X11)
% 0.37/0.54          | ~ (v1_relat_1 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.54  thf(t98_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X10 : $i]:
% 0.37/0.54         (((k7_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (X10))
% 0.37/0.54          | ~ (v1_relat_1 @ X10))),
% 0.37/0.54      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.37/0.54  thf(t148_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ B ) =>
% 0.37/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]:
% 0.37/0.54         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.37/0.54          | ~ (v1_relat_1 @ X2))),
% 0.37/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X9 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 0.37/0.54          | ~ (v1_relat_1 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X11 : $i]:
% 0.37/0.54         (~ (v2_funct_1 @ X11)
% 0.37/0.54          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.37/0.54          | ~ (v1_funct_1 @ X11)
% 0.37/0.54          | ~ (v1_relat_1 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.54  thf(t160_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( v1_relat_1 @ B ) =>
% 0.37/0.54           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.37/0.54             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X4 : $i, X5 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X4)
% 0.37/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.37/0.54              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.37/0.54          | ~ (v1_relat_1 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          != (k2_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('split', [status(esa)], ['9'])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.54  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.37/0.54         | ~ (v2_funct_1 @ sk_A)
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '31'])).
% 0.37/0.54  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('35', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.37/0.54           != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['25', '36'])).
% 0.37/0.54  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['24', '39'])).
% 0.37/0.54  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.37/0.54         | ~ (v2_funct_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '43'])).
% 0.37/0.54  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('46', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('47', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ sk_A))
% 0.37/0.54         <= (~
% 0.37/0.54             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54                = (k2_relat_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['19', '48'])).
% 0.37/0.54  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          = (k2_relat_1 @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (~
% 0.37/0.54       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          = (k2_relat_1 @ sk_A))) | 
% 0.37/0.54       ~
% 0.37/0.54       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          = (k2_relat_1 @ sk_A)))),
% 0.37/0.54      inference('split', [status(esa)], ['9'])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      (~
% 0.37/0.54       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.37/0.54          = (k2_relat_1 @ sk_A)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      ((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.37/0.54          != (k2_relat_1 @ sk_A))
% 0.37/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['18', '53'])).
% 0.37/0.54  thf('55', plain,
% 0.37/0.54      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.37/0.54        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '54'])).
% 0.37/0.54  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.37/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ sk_A)
% 0.37/0.54        | ((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '57'])).
% 0.37/0.54  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('61', plain,
% 0.37/0.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '60'])).
% 0.37/0.54  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('63', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.54  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
