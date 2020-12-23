%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6V8L0rOlQ7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 10.53s
% Output     : Refutation 10.53s
% Verified   : 
% Statistics : Number of formulae       :  200 (3123 expanded)
%              Number of leaves         :   30 (1108 expanded)
%              Depth                    :   15
%              Number of atoms          : 1944 (28092 expanded)
%              Number of equality atoms :  139 (2273 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X33 ) ) @ X33 )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X31 )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k5_relat_1 @ X25 @ ( k5_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('40',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X22 @ X23 )
        = ( k7_relat_1 @ X22 @ ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['55','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('71',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','79'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('81',plain,(
    ! [X34: $i] :
      ( ( ( k5_relat_1 @ X34 @ ( k6_relat_1 @ ( k2_relat_1 @ X34 ) ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('82',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('87',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X22 @ X23 )
        = ( k7_relat_1 @ X22 @ ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('96',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('97',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('98',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','79'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('102',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','79'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('107',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('108',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k5_relat_1 @ X25 @ ( k5_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('119',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('123',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('124',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['116','127'])).

thf('129',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','79'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','49','80','88','94','95','96','97','98','99','100','101','102','103','104','105','128','133','136','137','138','139','140','141'])).

thf('143',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('145',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X22 @ X23 )
        = ( k7_relat_1 @ X22 @ ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('146',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('150',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('154',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('155',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('156',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['144','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','49','80','88','94','95','96','97','98','99','100','101','102','103','104','105','128','133','136','137','138','139','140','141'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('164',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','49','80','88','94','95','96','97','98','99','100','101','102','103','104','105','128','133','136','137','138','139','140','141'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['161','162','164','165'])).

thf('167',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['143','166'])).

thf('168',plain,(
    $false ),
    inference(simplify,[status(thm)],['167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6V8L0rOlQ7
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 10.53/10.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.53/10.77  % Solved by: fo/fo7.sh
% 10.53/10.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.53/10.77  % done 7971 iterations in 10.308s
% 10.53/10.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.53/10.77  % SZS output start Refutation
% 10.53/10.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.53/10.77  thf(sk_B_type, type, sk_B: $i).
% 10.53/10.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.53/10.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 10.53/10.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.53/10.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 10.53/10.77  thf(sk_A_type, type, sk_A: $i).
% 10.53/10.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.53/10.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.53/10.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.53/10.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.53/10.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.53/10.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.53/10.77  thf(t94_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ B ) =>
% 10.53/10.77       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 10.53/10.77  thf('0', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf(t43_funct_1, conjecture,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 10.53/10.77       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.53/10.77  thf(zf_stmt_0, negated_conjecture,
% 10.53/10.77    (~( ![A:$i,B:$i]:
% 10.53/10.77        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 10.53/10.77          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 10.53/10.77    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 10.53/10.77  thf('1', plain,
% 10.53/10.77      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 10.53/10.77         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 10.53/10.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.77  thf('2', plain,
% 10.53/10.77      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.77          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 10.53/10.77        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['0', '1'])).
% 10.53/10.77  thf(fc3_funct_1, axiom,
% 10.53/10.77    (![A:$i]:
% 10.53/10.77     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 10.53/10.77       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 10.53/10.77  thf('3', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('4', plain,
% 10.53/10.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.77         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 10.53/10.77      inference('demod', [status(thm)], ['2', '3'])).
% 10.53/10.77  thf(t78_relat_1, axiom,
% 10.53/10.77    (![A:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ A ) =>
% 10.53/10.77       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 10.53/10.77  thf('5', plain,
% 10.53/10.77      (![X33 : $i]:
% 10.53/10.77         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X33)) @ X33) = (X33))
% 10.53/10.77          | ~ (v1_relat_1 @ X33))),
% 10.53/10.77      inference('cnf', [status(esa)], [t78_relat_1])).
% 10.53/10.77  thf(t17_xboole_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 10.53/10.77  thf('6', plain,
% 10.53/10.77      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 10.53/10.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 10.53/10.77  thf(t71_relat_1, axiom,
% 10.53/10.77    (![A:$i]:
% 10.53/10.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.53/10.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.53/10.77  thf('7', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf(t77_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ B ) =>
% 10.53/10.77       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 10.53/10.77         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 10.53/10.77  thf('8', plain,
% 10.53/10.77      (![X31 : $i, X32 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 10.53/10.77          | ((k5_relat_1 @ (k6_relat_1 @ X32) @ X31) = (X31))
% 10.53/10.77          | ~ (v1_relat_1 @ X31))),
% 10.53/10.77      inference('cnf', [status(esa)], [t77_relat_1])).
% 10.53/10.77  thf('9', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ X0 @ X1)
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77              = (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['7', '8'])).
% 10.53/10.77  thf('10', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('11', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ X0 @ X1)
% 10.53/10.77          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77              = (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['9', '10'])).
% 10.53/10.77  thf('12', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 10.53/10.77           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['6', '11'])).
% 10.53/10.77  thf(t55_relat_1, axiom,
% 10.53/10.77    (![A:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ A ) =>
% 10.53/10.77       ( ![B:$i]:
% 10.53/10.77         ( ( v1_relat_1 @ B ) =>
% 10.53/10.77           ( ![C:$i]:
% 10.53/10.77             ( ( v1_relat_1 @ C ) =>
% 10.53/10.77               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 10.53/10.77                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 10.53/10.77  thf('13', plain,
% 10.53/10.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X24)
% 10.53/10.77          | ((k5_relat_1 @ (k5_relat_1 @ X25 @ X24) @ X26)
% 10.53/10.77              = (k5_relat_1 @ X25 @ (k5_relat_1 @ X24 @ X26)))
% 10.53/10.77          | ~ (v1_relat_1 @ X26)
% 10.53/10.77          | ~ (v1_relat_1 @ X25))),
% 10.53/10.77      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.53/10.77  thf(t76_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ B ) =>
% 10.53/10.77       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 10.53/10.77         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 10.53/10.77  thf('14', plain,
% 10.53/10.77      (![X29 : $i, X30 : $i]:
% 10.53/10.77         ((r1_tarski @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) @ X29)
% 10.53/10.77          | ~ (v1_relat_1 @ X29))),
% 10.53/10.77      inference('cnf', [status(esa)], [t76_relat_1])).
% 10.53/10.77  thf(d10_xboole_0, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.53/10.77  thf('15', plain,
% 10.53/10.77      (![X0 : $i, X2 : $i]:
% 10.53/10.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.53/10.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.53/10.77  thf('16', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X0)
% 10.53/10.77          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['14', '15'])).
% 10.53/10.77  thf('17', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 10.53/10.77             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ((k5_relat_1 @ X2 @ X1)
% 10.53/10.77              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['13', '16'])).
% 10.53/10.77  thf('18', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('19', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 10.53/10.77             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ((k5_relat_1 @ X2 @ X1)
% 10.53/10.77              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['17', '18'])).
% 10.53/10.77  thf('20', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 10.53/10.77             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 10.53/10.77              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 10.53/10.77                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ~ (v1_relat_1 @ X2))),
% 10.53/10.77      inference('sup-', [status(thm)], ['12', '19'])).
% 10.53/10.77  thf('21', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('22', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 10.53/10.77             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 10.53/10.77              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 10.53/10.77                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ X2))),
% 10.53/10.77      inference('demod', [status(thm)], ['20', '21'])).
% 10.53/10.77  thf('23', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ 
% 10.53/10.77             (k5_relat_1 @ 
% 10.53/10.77              (k6_relat_1 @ 
% 10.53/10.77               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 10.53/10.77              (k6_relat_1 @ X1)) @ 
% 10.53/10.77             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ 
% 10.53/10.77               (k6_relat_1 @ 
% 10.53/10.77                (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))
% 10.53/10.77          | ((k5_relat_1 @ 
% 10.53/10.77              (k6_relat_1 @ 
% 10.53/10.77               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 10.53/10.77              (k6_relat_1 @ X1))
% 10.53/10.77              = (k5_relat_1 @ 
% 10.53/10.77                 (k5_relat_1 @ 
% 10.53/10.77                  (k6_relat_1 @ 
% 10.53/10.77                   (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 10.53/10.77                  (k6_relat_1 @ X1)) @ 
% 10.53/10.77                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 10.53/10.77          | ~ (v1_relat_1 @ 
% 10.53/10.77               (k5_relat_1 @ 
% 10.53/10.77                (k6_relat_1 @ 
% 10.53/10.77                 (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 10.53/10.77                (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['5', '22'])).
% 10.53/10.77  thf('24', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('25', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('26', plain,
% 10.53/10.77      (![X29 : $i, X30 : $i]:
% 10.53/10.77         ((r1_tarski @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) @ X29)
% 10.53/10.77          | ~ (v1_relat_1 @ X29))),
% 10.53/10.77      inference('cnf', [status(esa)], [t76_relat_1])).
% 10.53/10.77  thf(t28_xboole_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 10.53/10.77  thf('27', plain,
% 10.53/10.77      (![X5 : $i, X6 : $i]:
% 10.53/10.77         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 10.53/10.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.53/10.77  thf('28', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X0)
% 10.53/10.77          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 10.53/10.77              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['26', '27'])).
% 10.53/10.77  thf(commutativity_k2_tarski, axiom,
% 10.53/10.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 10.53/10.77  thf('29', plain,
% 10.53/10.77      (![X11 : $i, X12 : $i]:
% 10.53/10.77         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 10.53/10.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 10.53/10.77  thf(t12_setfam_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.53/10.77  thf('30', plain,
% 10.53/10.77      (![X15 : $i, X16 : $i]:
% 10.53/10.77         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 10.53/10.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.53/10.77  thf('31', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['29', '30'])).
% 10.53/10.77  thf('32', plain,
% 10.53/10.77      (![X15 : $i, X16 : $i]:
% 10.53/10.77         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 10.53/10.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.53/10.77  thf('33', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['31', '32'])).
% 10.53/10.77  thf('34', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X0)
% 10.53/10.77          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 10.53/10.77              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('demod', [status(thm)], ['28', '33'])).
% 10.53/10.77  thf('35', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 10.53/10.77            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['25', '34'])).
% 10.53/10.77  thf('36', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('37', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('38', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 10.53/10.77           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['35', '36', '37'])).
% 10.53/10.77  thf('39', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('40', plain,
% 10.53/10.77      (![X29 : $i, X30 : $i]:
% 10.53/10.77         ((r1_tarski @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) @ X29)
% 10.53/10.77          | ~ (v1_relat_1 @ X29))),
% 10.53/10.77      inference('cnf', [status(esa)], [t76_relat_1])).
% 10.53/10.77  thf('41', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 10.53/10.77           (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['39', '40'])).
% 10.53/10.77  thf('42', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('43', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('44', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 10.53/10.77  thf('45', plain,
% 10.53/10.77      (![X5 : $i, X6 : $i]:
% 10.53/10.77         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 10.53/10.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.53/10.77  thf('46', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 10.53/10.77           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('sup-', [status(thm)], ['44', '45'])).
% 10.53/10.77  thf('47', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['31', '32'])).
% 10.53/10.77  thf('48', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 10.53/10.77           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['46', '47'])).
% 10.53/10.77  thf('49', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf(t100_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i,C:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ C ) =>
% 10.53/10.77       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 10.53/10.77         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 10.53/10.77  thf('50', plain,
% 10.53/10.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X19 @ X20) @ X21)
% 10.53/10.77            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ X20 @ X21)))
% 10.53/10.77          | ~ (v1_relat_1 @ X19))),
% 10.53/10.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 10.53/10.77  thf('51', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['31', '32'])).
% 10.53/10.77  thf('52', plain,
% 10.53/10.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X19 @ X20) @ X21)
% 10.53/10.77            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ X20 @ X21)))
% 10.53/10.77          | ~ (v1_relat_1 @ X19))),
% 10.53/10.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 10.53/10.77  thf('53', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 10.53/10.77            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ X2))),
% 10.53/10.77      inference('sup+', [status(thm)], ['51', '52'])).
% 10.53/10.77  thf('54', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 10.53/10.77            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X2))),
% 10.53/10.77      inference('sup+', [status(thm)], ['50', '53'])).
% 10.53/10.77  thf('55', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X2)
% 10.53/10.77          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 10.53/10.77              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 10.53/10.77      inference('simplify', [status(thm)], ['54'])).
% 10.53/10.77  thf('56', plain,
% 10.53/10.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X19 @ X20) @ X21)
% 10.53/10.77            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ X20 @ X21)))
% 10.53/10.77          | ~ (v1_relat_1 @ X19))),
% 10.53/10.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 10.53/10.77  thf('57', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf(t192_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ B ) =>
% 10.53/10.77       ( ( k7_relat_1 @ B @ A ) =
% 10.53/10.77         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 10.53/10.77  thf('58', plain,
% 10.53/10.77      (![X22 : $i, X23 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X22 @ X23)
% 10.53/10.77            = (k7_relat_1 @ X22 @ (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23)))
% 10.53/10.77          | ~ (v1_relat_1 @ X22))),
% 10.53/10.77      inference('cnf', [status(esa)], [t192_relat_1])).
% 10.53/10.77  thf('59', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 10.53/10.77            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['57', '58'])).
% 10.53/10.77  thf('60', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('61', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['59', '60'])).
% 10.53/10.77  thf('62', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 10.53/10.77            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ X2))),
% 10.53/10.77      inference('sup+', [status(thm)], ['51', '52'])).
% 10.53/10.77  thf('63', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 10.53/10.77            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['61', '62'])).
% 10.53/10.77  thf('64', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('65', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['63', '64'])).
% 10.53/10.77  thf('66', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ 
% 10.53/10.77            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2)
% 10.53/10.77            = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['56', '65'])).
% 10.53/10.77  thf('67', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('68', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ 
% 10.53/10.77           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['66', '67'])).
% 10.53/10.77  thf('69', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ 
% 10.53/10.77            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X1) @ X0)
% 10.53/10.77            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['55', '68'])).
% 10.53/10.77  thf('70', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['63', '64'])).
% 10.53/10.77  thf('71', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('72', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X0)
% 10.53/10.77          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 10.53/10.77              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('demod', [status(thm)], ['28', '33'])).
% 10.53/10.77  thf(fc1_relat_1, axiom,
% 10.53/10.77    (![A:$i,B:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.53/10.77  thf('73', plain,
% 10.53/10.77      (![X17 : $i, X18 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k3_xboole_0 @ X17 @ X18)))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc1_relat_1])).
% 10.53/10.77  thf('74', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ~ (v1_relat_1 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['72', '73'])).
% 10.53/10.77  thf('75', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X1)
% 10.53/10.77          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 10.53/10.77      inference('simplify', [status(thm)], ['74'])).
% 10.53/10.77  thf('76', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['71', '75'])).
% 10.53/10.77  thf('77', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('78', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('79', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['76', '77', '78'])).
% 10.53/10.77  thf('80', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['69', '70', '79'])).
% 10.53/10.77  thf(t80_relat_1, axiom,
% 10.53/10.77    (![A:$i]:
% 10.53/10.77     ( ( v1_relat_1 @ A ) =>
% 10.53/10.77       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 10.53/10.77  thf('81', plain,
% 10.53/10.77      (![X34 : $i]:
% 10.53/10.77         (((k5_relat_1 @ X34 @ (k6_relat_1 @ (k2_relat_1 @ X34))) = (X34))
% 10.53/10.77          | ~ (v1_relat_1 @ X34))),
% 10.53/10.77      inference('cnf', [status(esa)], [t80_relat_1])).
% 10.53/10.77  thf('82', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('83', plain,
% 10.53/10.77      (![X0 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 10.53/10.77            = (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 10.53/10.77      inference('sup+', [status(thm)], ['81', '82'])).
% 10.53/10.77  thf('84', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('85', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('86', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('87', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('88', plain,
% 10.53/10.77      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 10.53/10.77  thf('89', plain,
% 10.53/10.77      (![X22 : $i, X23 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X22 @ X23)
% 10.53/10.77            = (k7_relat_1 @ X22 @ (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23)))
% 10.53/10.77          | ~ (v1_relat_1 @ X22))),
% 10.53/10.77      inference('cnf', [status(esa)], [t192_relat_1])).
% 10.53/10.77  thf('90', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 10.53/10.77  thf('91', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 10.53/10.77           (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['89', '90'])).
% 10.53/10.77  thf('92', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('93', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('94', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 10.53/10.77          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['91', '92', '93'])).
% 10.53/10.77  thf('95', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('96', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('97', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('98', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('99', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('100', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['69', '70', '79'])).
% 10.53/10.77  thf('101', plain,
% 10.53/10.77      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 10.53/10.77  thf('102', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('103', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('104', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['69', '70', '79'])).
% 10.53/10.77  thf('105', plain,
% 10.53/10.77      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 10.53/10.77  thf('106', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('107', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('108', plain,
% 10.53/10.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X24)
% 10.53/10.77          | ((k5_relat_1 @ (k5_relat_1 @ X25 @ X24) @ X26)
% 10.53/10.77              = (k5_relat_1 @ X25 @ (k5_relat_1 @ X24 @ X26)))
% 10.53/10.77          | ~ (v1_relat_1 @ X26)
% 10.53/10.77          | ~ (v1_relat_1 @ X25))),
% 10.53/10.77      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.53/10.77  thf('109', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 10.53/10.77            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['107', '108'])).
% 10.53/10.77  thf('110', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('111', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 10.53/10.77            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X1))),
% 10.53/10.77      inference('demod', [status(thm)], ['109', '110'])).
% 10.53/10.77  thf('112', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 10.53/10.77              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 10.53/10.77      inference('simplify', [status(thm)], ['111'])).
% 10.53/10.77  thf('113', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.77            (k6_relat_1 @ X1))
% 10.53/10.77            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 10.53/10.77               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['106', '112'])).
% 10.53/10.77  thf('114', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('115', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('116', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.77           (k6_relat_1 @ X1))
% 10.53/10.77           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 10.53/10.77              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 10.53/10.77  thf('117', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('118', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X1)
% 10.53/10.77          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 10.53/10.77              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 10.53/10.77      inference('simplify', [status(thm)], ['111'])).
% 10.53/10.77  thf('119', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('120', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 10.53/10.77            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ X2)
% 10.53/10.77          | ~ (v1_relat_1 @ X0)
% 10.53/10.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['118', '119'])).
% 10.53/10.77  thf('121', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.77          | ((k7_relat_1 @ 
% 10.53/10.77              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 10.53/10.77              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.77                 (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['117', '120'])).
% 10.53/10.77  thf('122', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['76', '77', '78'])).
% 10.53/10.77  thf('123', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('124', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('125', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('126', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.77           (k6_relat_1 @ X1))
% 10.53/10.77           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 10.53/10.77              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 10.53/10.77  thf('127', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 10.53/10.77           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 10.53/10.77              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)],
% 10.53/10.77                ['121', '122', '123', '124', '125', '126'])).
% 10.53/10.77  thf('128', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.77           (k6_relat_1 @ X1))
% 10.53/10.77           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 10.53/10.77      inference('demod', [status(thm)], ['116', '127'])).
% 10.53/10.77  thf('129', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('130', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 10.53/10.77           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['6', '11'])).
% 10.53/10.77  thf('131', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 10.53/10.77            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 10.53/10.77      inference('sup+', [status(thm)], ['129', '130'])).
% 10.53/10.77  thf('132', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('133', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['131', '132'])).
% 10.53/10.77  thf('134', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['31', '32'])).
% 10.53/10.77  thf('135', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['131', '132'])).
% 10.53/10.77  thf('136', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('sup+', [status(thm)], ['134', '135'])).
% 10.53/10.77  thf('137', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('138', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('139', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['69', '70', '79'])).
% 10.53/10.77  thf('140', plain,
% 10.53/10.77      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 10.53/10.77  thf('141', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 10.53/10.77      inference('demod', [status(thm)], ['76', '77', '78'])).
% 10.53/10.77  thf('142', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)],
% 10.53/10.77                ['23', '24', '49', '80', '88', '94', '95', '96', '97', '98', 
% 10.53/10.77                 '99', '100', '101', '102', '103', '104', '105', '128', '133', 
% 10.53/10.77                 '136', '137', '138', '139', '140', '141'])).
% 10.53/10.77  thf('143', plain,
% 10.53/10.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.77         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 10.53/10.77      inference('demod', [status(thm)], ['4', '142'])).
% 10.53/10.77  thf('144', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['31', '32'])).
% 10.53/10.77  thf('145', plain,
% 10.53/10.77      (![X22 : $i, X23 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X22 @ X23)
% 10.53/10.77            = (k7_relat_1 @ X22 @ (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23)))
% 10.53/10.77          | ~ (v1_relat_1 @ X22))),
% 10.53/10.77      inference('cnf', [status(esa)], [t192_relat_1])).
% 10.53/10.77  thf('146', plain,
% 10.53/10.77      (![X35 : $i, X36 : $i]:
% 10.53/10.77         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 10.53/10.77          | ~ (v1_relat_1 @ X36))),
% 10.53/10.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.77  thf('147', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (v1_relat_1 @ X0)
% 10.53/10.77          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['14', '15'])).
% 10.53/10.77  thf('148', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ((k6_relat_1 @ X0)
% 10.53/10.77              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['146', '147'])).
% 10.53/10.77  thf('149', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('150', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('151', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ((k6_relat_1 @ X0)
% 10.53/10.77              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('demod', [status(thm)], ['148', '149', '150'])).
% 10.53/10.77  thf('152', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ 
% 10.53/10.77             (k6_relat_1 @ 
% 10.53/10.77              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.77          | ((k6_relat_1 @ 
% 10.53/10.77              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 10.53/10.77              = (k5_relat_1 @ 
% 10.53/10.77                 (k6_relat_1 @ 
% 10.53/10.77                  (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 10.53/10.77                 (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('sup-', [status(thm)], ['145', '151'])).
% 10.53/10.77  thf('153', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('154', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 10.53/10.77      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.77  thf('155', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('156', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.53/10.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.77  thf('157', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 10.53/10.77              = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.53/10.77                 (k6_relat_1 @ X1))))),
% 10.53/10.77      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 10.53/10.77  thf('158', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('sup+', [status(thm)], ['38', '48'])).
% 10.53/10.77  thf('159', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)], ['59', '60'])).
% 10.53/10.77  thf('160', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 10.53/10.77          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 10.53/10.77              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 10.53/10.77      inference('demod', [status(thm)], ['157', '158', '159'])).
% 10.53/10.77  thf('161', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.53/10.77             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 10.53/10.77          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 10.53/10.77              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 10.53/10.77      inference('sup-', [status(thm)], ['144', '160'])).
% 10.53/10.77  thf('162', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)],
% 10.53/10.77                ['23', '24', '49', '80', '88', '94', '95', '96', '97', '98', 
% 10.53/10.77                 '99', '100', '101', '102', '103', '104', '105', '128', '133', 
% 10.53/10.77                 '136', '137', '138', '139', '140', '141'])).
% 10.53/10.77  thf('163', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 10.53/10.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.53/10.77  thf('164', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.53/10.77      inference('simplify', [status(thm)], ['163'])).
% 10.53/10.77  thf('165', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 10.53/10.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.53/10.77      inference('demod', [status(thm)],
% 10.53/10.77                ['23', '24', '49', '80', '88', '94', '95', '96', '97', '98', 
% 10.53/10.77                 '99', '100', '101', '102', '103', '104', '105', '128', '133', 
% 10.53/10.77                 '136', '137', '138', '139', '140', '141'])).
% 10.53/10.77  thf('166', plain,
% 10.53/10.77      (![X0 : $i, X1 : $i]:
% 10.53/10.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 10.53/10.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 10.53/10.77      inference('demod', [status(thm)], ['161', '162', '164', '165'])).
% 10.53/10.77  thf('167', plain,
% 10.53/10.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.77         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 10.53/10.77      inference('demod', [status(thm)], ['143', '166'])).
% 10.53/10.77  thf('168', plain, ($false), inference('simplify', [status(thm)], ['167'])).
% 10.53/10.77  
% 10.53/10.77  % SZS output end Refutation
% 10.53/10.77  
% 10.53/10.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
