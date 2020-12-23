%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJ1XYC7S5S

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:01 EST 2020

% Result     : Theorem 3.60s
% Output     : Refutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 355 expanded)
%              Number of leaves         :   23 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  892 (3190 expanded)
%              Number of equality atoms :   65 ( 235 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['17','29','30','31'])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('43',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','58','59','60','61','62','71','72','73','74'])).

thf('76',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJ1XYC7S5S
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.60/3.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.60/3.80  % Solved by: fo/fo7.sh
% 3.60/3.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.60/3.80  % done 3414 iterations in 3.346s
% 3.60/3.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.60/3.80  % SZS output start Refutation
% 3.60/3.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.60/3.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.60/3.80  thf(sk_A_type, type, sk_A: $i).
% 3.60/3.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.60/3.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.60/3.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.60/3.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.60/3.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.60/3.80  thf(sk_B_type, type, sk_B: $i).
% 3.60/3.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.60/3.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.60/3.80  thf(t94_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ B ) =>
% 3.60/3.80       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.60/3.80  thf('0', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf(t43_funct_1, conjecture,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.60/3.80       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.60/3.80  thf(zf_stmt_0, negated_conjecture,
% 3.60/3.80    (~( ![A:$i,B:$i]:
% 3.60/3.80        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.60/3.80          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 3.60/3.80    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 3.60/3.80  thf('1', plain,
% 3.60/3.80      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 3.60/3.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.60/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.60/3.80  thf('2', plain,
% 3.60/3.80      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.60/3.80          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 3.60/3.80        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['0', '1'])).
% 3.60/3.80  thf(fc3_funct_1, axiom,
% 3.60/3.80    (![A:$i]:
% 3.60/3.80     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.60/3.80       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.60/3.80  thf('3', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('4', plain,
% 3.60/3.80      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.60/3.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.60/3.80      inference('demod', [status(thm)], ['2', '3'])).
% 3.60/3.80  thf('5', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf('6', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf(t76_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ B ) =>
% 3.60/3.80       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 3.60/3.80         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 3.60/3.80  thf('7', plain,
% 3.60/3.80      (![X20 : $i, X21 : $i]:
% 3.60/3.80         ((r1_tarski @ (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)) @ X20)
% 3.60/3.80          | ~ (v1_relat_1 @ X20))),
% 3.60/3.80      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.60/3.80  thf(t71_relat_1, axiom,
% 3.60/3.80    (![A:$i]:
% 3.60/3.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.60/3.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.60/3.80  thf('8', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.60/3.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.60/3.80  thf(t79_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ B ) =>
% 3.60/3.80       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.60/3.80         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 3.60/3.80  thf('9', plain,
% 3.60/3.80      (![X23 : $i, X24 : $i]:
% 3.60/3.80         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 3.60/3.80          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 3.60/3.80          | ~ (v1_relat_1 @ X23))),
% 3.60/3.80      inference('cnf', [status(esa)], [t79_relat_1])).
% 3.60/3.80  thf('10', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (r1_tarski @ X0 @ X1)
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.60/3.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.60/3.80              = (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['8', '9'])).
% 3.60/3.80  thf('11', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('12', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (r1_tarski @ X0 @ X1)
% 3.60/3.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.60/3.80              = (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['10', '11'])).
% 3.60/3.80  thf('13', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ X0)
% 3.60/3.80          | ((k5_relat_1 @ 
% 3.60/3.80              (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 3.60/3.80              (k6_relat_1 @ X0))
% 3.60/3.80              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.60/3.80      inference('sup-', [status(thm)], ['7', '12'])).
% 3.60/3.80  thf('14', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.60/3.80            (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.60/3.80            = (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.60/3.80          | ~ (v1_relat_1 @ X1))),
% 3.60/3.80      inference('sup+', [status(thm)], ['6', '13'])).
% 3.60/3.80  thf('15', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('16', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.60/3.80            (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.60/3.80            = (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.60/3.80          | ~ (v1_relat_1 @ X1))),
% 3.60/3.80      inference('demod', [status(thm)], ['14', '15'])).
% 3.60/3.80  thf('17', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k7_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ X0)) @ 
% 3.60/3.80            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80            = (k6_relat_1 @ 
% 3.60/3.80               (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['5', '16'])).
% 3.60/3.80  thf('18', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf('19', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf('20', plain,
% 3.60/3.80      (![X20 : $i, X21 : $i]:
% 3.60/3.80         ((r1_tarski @ (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)) @ X20)
% 3.60/3.80          | ~ (v1_relat_1 @ X20))),
% 3.60/3.80      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.60/3.80  thf('21', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.60/3.80           (k6_relat_1 @ X0))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['19', '20'])).
% 3.60/3.80  thf('22', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('23', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('24', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 3.60/3.80      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.60/3.80  thf('25', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (r1_tarski @ X0 @ X1)
% 3.60/3.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.60/3.80              = (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['10', '11'])).
% 3.60/3.80  thf('26', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k5_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 3.60/3.80           (k6_relat_1 @ (k6_relat_1 @ X0)))
% 3.60/3.80           = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['24', '25'])).
% 3.60/3.80  thf('27', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k7_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ X0)) @ 
% 3.60/3.80            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80            = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ X0))))),
% 3.60/3.80      inference('sup+', [status(thm)], ['18', '26'])).
% 3.60/3.80  thf('28', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('29', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ X0)) @ 
% 3.60/3.80           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80           = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['27', '28'])).
% 3.60/3.80  thf('30', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('31', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('32', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80           = (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 3.60/3.80      inference('demod', [status(thm)], ['17', '29', '30', '31'])).
% 3.60/3.80  thf('33', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 3.60/3.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.60/3.80  thf('34', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.60/3.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['32', '33'])).
% 3.60/3.80  thf('35', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 3.60/3.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.60/3.80  thf('36', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.60/3.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['34', '35'])).
% 3.60/3.80  thf('37', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf(t55_relat_1, axiom,
% 3.60/3.80    (![A:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ A ) =>
% 3.60/3.80       ( ![B:$i]:
% 3.60/3.80         ( ( v1_relat_1 @ B ) =>
% 3.60/3.80           ( ![C:$i]:
% 3.60/3.80             ( ( v1_relat_1 @ C ) =>
% 3.60/3.80               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.60/3.80                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.60/3.80  thf('38', plain,
% 3.60/3.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ X15)
% 3.60/3.80          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 3.60/3.80              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 3.60/3.80          | ~ (v1_relat_1 @ X17)
% 3.60/3.80          | ~ (v1_relat_1 @ X16))),
% 3.60/3.80      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.60/3.80  thf('39', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.60/3.80         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.60/3.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.60/3.80          | ~ (v1_relat_1 @ X1)
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.60/3.80          | ~ (v1_relat_1 @ X2)
% 3.60/3.80          | ~ (v1_relat_1 @ X1))),
% 3.60/3.80      inference('sup+', [status(thm)], ['37', '38'])).
% 3.60/3.80  thf('40', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('41', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.60/3.80         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.60/3.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.60/3.80          | ~ (v1_relat_1 @ X1)
% 3.60/3.80          | ~ (v1_relat_1 @ X2)
% 3.60/3.80          | ~ (v1_relat_1 @ X1))),
% 3.60/3.80      inference('demod', [status(thm)], ['39', '40'])).
% 3.60/3.80  thf('42', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ X2)
% 3.60/3.80          | ~ (v1_relat_1 @ X1)
% 3.60/3.80          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.60/3.80              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.60/3.80      inference('simplify', [status(thm)], ['41'])).
% 3.60/3.80  thf(t78_relat_1, axiom,
% 3.60/3.80    (![A:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ A ) =>
% 3.60/3.80       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 3.60/3.80  thf('43', plain,
% 3.60/3.80      (![X22 : $i]:
% 3.60/3.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 3.60/3.80          | ~ (v1_relat_1 @ X22))),
% 3.60/3.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 3.60/3.80  thf('44', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k5_relat_1 @ 
% 3.60/3.80            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 3.60/3.80            = (k5_relat_1 @ X1 @ X0))
% 3.60/3.80          | ~ (v1_relat_1 @ X1)
% 3.60/3.80          | ~ (v1_relat_1 @ X0)
% 3.60/3.80          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['42', '43'])).
% 3.60/3.80  thf('45', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.60/3.80          | ((k5_relat_1 @ 
% 3.60/3.80              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.60/3.80               (k1_relat_1 @ 
% 3.60/3.80                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 3.60/3.80              (k6_relat_1 @ X1))
% 3.60/3.80              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 3.60/3.80      inference('sup-', [status(thm)], ['36', '44'])).
% 3.60/3.80  thf('46', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ X0)) @ 
% 3.60/3.80           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80           = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['27', '28'])).
% 3.60/3.80  thf('47', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 3.60/3.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.60/3.80  thf(t90_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ B ) =>
% 3.60/3.80       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 3.60/3.80         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.60/3.80  thf('48', plain,
% 3.60/3.80      (![X25 : $i, X26 : $i]:
% 3.60/3.80         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 3.60/3.80            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 3.60/3.80          | ~ (v1_relat_1 @ X25))),
% 3.60/3.80      inference('cnf', [status(esa)], [t90_relat_1])).
% 3.60/3.80  thf('49', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 3.60/3.80            = (k3_xboole_0 @ X0 @ X1))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['47', '48'])).
% 3.60/3.80  thf('50', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('51', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 3.60/3.80           = (k3_xboole_0 @ X0 @ X1))),
% 3.60/3.80      inference('demod', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf('52', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.60/3.80           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 3.60/3.80              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['46', '51'])).
% 3.60/3.80  thf('53', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 3.60/3.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.60/3.80  thf('54', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.60/3.80           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 3.60/3.80              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['52', '53'])).
% 3.60/3.80  thf(fc1_relat_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]:
% 3.60/3.80     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.60/3.80  thf('55', plain,
% 3.60/3.80      (![X13 : $i, X14 : $i]:
% 3.60/3.80         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k3_xboole_0 @ X13 @ X14)))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc1_relat_1])).
% 3.60/3.80  thf('56', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['54', '55'])).
% 3.60/3.80  thf('57', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('58', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.60/3.80      inference('demod', [status(thm)], ['56', '57'])).
% 3.60/3.80  thf('59', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('60', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('61', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.60/3.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['34', '35'])).
% 3.60/3.80  thf('62', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 3.60/3.80           = (k3_xboole_0 @ X0 @ X1))),
% 3.60/3.80      inference('demod', [status(thm)], ['49', '50'])).
% 3.60/3.80  thf('63', plain,
% 3.60/3.80      (![X27 : $i, X28 : $i]:
% 3.60/3.80         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 3.60/3.80          | ~ (v1_relat_1 @ X28))),
% 3.60/3.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.60/3.80  thf(commutativity_k3_xboole_0, axiom,
% 3.60/3.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.60/3.80  thf('64', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.60/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.60/3.80  thf(t17_xboole_1, axiom,
% 3.60/3.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.60/3.80  thf('65', plain,
% 3.60/3.80      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 3.60/3.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.60/3.80  thf('66', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (~ (r1_tarski @ X0 @ X1)
% 3.60/3.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.60/3.80              = (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('demod', [status(thm)], ['10', '11'])).
% 3.60/3.80  thf('67', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.60/3.80           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.60/3.80      inference('sup-', [status(thm)], ['65', '66'])).
% 3.60/3.80  thf('68', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.60/3.80           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['64', '67'])).
% 3.60/3.80  thf('69', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.60/3.80            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.60/3.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.60/3.80      inference('sup+', [status(thm)], ['63', '68'])).
% 3.60/3.80  thf('70', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.60/3.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.60/3.80  thf('71', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.60/3.80           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['69', '70'])).
% 3.60/3.80  thf('72', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.60/3.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['34', '35'])).
% 3.60/3.80  thf('73', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.60/3.80           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['69', '70'])).
% 3.60/3.80  thf('74', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.60/3.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 3.60/3.80      inference('demod', [status(thm)], ['34', '35'])).
% 3.60/3.80  thf('75', plain,
% 3.60/3.80      (![X0 : $i, X1 : $i]:
% 3.60/3.80         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 3.60/3.80           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.60/3.80      inference('demod', [status(thm)],
% 3.60/3.80                ['45', '58', '59', '60', '61', '62', '71', '72', '73', '74'])).
% 3.60/3.80  thf('76', plain,
% 3.60/3.80      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.60/3.80         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.60/3.80      inference('demod', [status(thm)], ['4', '75'])).
% 3.60/3.80  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 3.60/3.80  
% 3.60/3.80  % SZS output end Refutation
% 3.60/3.80  
% 3.60/3.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
