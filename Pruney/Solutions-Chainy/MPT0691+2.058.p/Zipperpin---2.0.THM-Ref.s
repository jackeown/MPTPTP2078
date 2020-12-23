%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwASpjD0oW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 231 expanded)
%              Number of leaves         :   28 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  807 (1953 expanded)
%              Number of equality atoms :   54 ( 146 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X21 ) @ X22 )
        = ( k7_relat_1 @ X23 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) )
        = ( k7_relat_1 @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ ( k1_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X44 @ X43 ) @ X45 )
        = ( k3_xboole_0 @ X43 @ ( k10_relat_1 @ X44 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) )
        = ( k7_relat_1 @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ ( k1_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) )
        = ( k7_relat_1 @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ ( k1_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('37',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('38',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('39',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39','40','41'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) ) @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) ) @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['28','53','54'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) )
        = ( k10_relat_1 @ X33 @ ( k1_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X29 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwASpjD0oW
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.68/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.68/1.92  % Solved by: fo/fo7.sh
% 1.68/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.92  % done 2039 iterations in 1.431s
% 1.68/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.68/1.92  % SZS output start Refutation
% 1.68/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.68/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.68/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.68/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.68/1.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.68/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.68/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.68/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.68/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.68/1.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.68/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.68/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.68/1.92  thf(t146_funct_1, conjecture,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ B ) =>
% 1.68/1.92       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.68/1.92         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.68/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.92    (~( ![A:$i,B:$i]:
% 1.68/1.92        ( ( v1_relat_1 @ B ) =>
% 1.68/1.92          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.68/1.92            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.68/1.92    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.68/1.92  thf('0', plain,
% 1.68/1.92      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(t71_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.68/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.68/1.92  thf('1', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf(t98_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) =>
% 1.68/1.92       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 1.68/1.92  thf('2', plain,
% 1.68/1.92      (![X40 : $i]:
% 1.68/1.92         (((k7_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (X40))
% 1.68/1.92          | ~ (v1_relat_1 @ X40))),
% 1.68/1.92      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.68/1.92  thf('3', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 1.68/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['1', '2'])).
% 1.68/1.92  thf(fc3_funct_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.68/1.92       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.68/1.92  thf('4', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('5', plain,
% 1.68/1.92      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.68/1.92      inference('demod', [status(thm)], ['3', '4'])).
% 1.68/1.92  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(t102_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ C ) =>
% 1.68/1.92       ( ( r1_tarski @ A @ B ) =>
% 1.68/1.92         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 1.68/1.92  thf('7', plain,
% 1.68/1.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.68/1.92         (~ (r1_tarski @ X21 @ X22)
% 1.68/1.92          | ~ (v1_relat_1 @ X23)
% 1.68/1.92          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X21) @ X22)
% 1.68/1.92              = (k7_relat_1 @ X23 @ X21)))),
% 1.68/1.92      inference('cnf', [status(esa)], [t102_relat_1])).
% 1.68/1.92  thf('8', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92            = (k7_relat_1 @ X0 @ sk_A))
% 1.68/1.92          | ~ (v1_relat_1 @ X0))),
% 1.68/1.92      inference('sup-', [status(thm)], ['6', '7'])).
% 1.68/1.92  thf('9', plain,
% 1.68/1.92      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92          = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A))
% 1.68/1.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['5', '8'])).
% 1.68/1.92  thf('10', plain,
% 1.68/1.92      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.68/1.92      inference('demod', [status(thm)], ['3', '4'])).
% 1.68/1.92  thf('11', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('12', plain,
% 1.68/1.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92         = (k6_relat_1 @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.68/1.92  thf(t189_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) =>
% 1.68/1.92       ( ![B:$i]:
% 1.68/1.92         ( ( v1_relat_1 @ B ) =>
% 1.68/1.92           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 1.68/1.92             ( k7_relat_1 @
% 1.68/1.92               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 1.68/1.92  thf('13', plain,
% 1.68/1.92      (![X34 : $i, X35 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X34)
% 1.68/1.92          | ((k7_relat_1 @ X35 @ (k1_relat_1 @ X34))
% 1.68/1.92              = (k7_relat_1 @ X35 @ 
% 1.68/1.92                 (k1_relat_1 @ (k7_relat_1 @ X34 @ (k1_relat_1 @ X35)))))
% 1.68/1.92          | ~ (v1_relat_1 @ X35))),
% 1.68/1.92      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.68/1.92  thf(t148_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ B ) =>
% 1.68/1.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.68/1.92  thf('14', plain,
% 1.68/1.92      (![X24 : $i, X25 : $i]:
% 1.68/1.92         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 1.68/1.92          | ~ (v1_relat_1 @ X24))),
% 1.68/1.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.68/1.92  thf('15', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.68/1.92            = (k9_relat_1 @ X1 @ 
% 1.68/1.92               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X1))),
% 1.68/1.92      inference('sup+', [status(thm)], ['13', '14'])).
% 1.68/1.92  thf('16', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.68/1.92              = (k9_relat_1 @ X1 @ 
% 1.68/1.92                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))))),
% 1.68/1.92      inference('simplify', [status(thm)], ['15'])).
% 1.68/1.92  thf('17', plain,
% 1.68/1.92      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))))
% 1.68/1.92          = (k9_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_B)
% 1.68/1.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['12', '16'])).
% 1.68/1.92  thf('18', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('19', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('21', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('22', plain,
% 1.68/1.92      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 1.68/1.92  thf(t139_funct_1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ C ) =>
% 1.68/1.92       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.68/1.92         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.68/1.92  thf('23', plain,
% 1.68/1.92      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.68/1.92         (((k10_relat_1 @ (k7_relat_1 @ X44 @ X43) @ X45)
% 1.68/1.92            = (k3_xboole_0 @ X43 @ (k10_relat_1 @ X44 @ X45)))
% 1.68/1.92          | ~ (v1_relat_1 @ X44))),
% 1.68/1.92      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.68/1.92  thf(t169_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) =>
% 1.68/1.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.68/1.92  thf('24', plain,
% 1.68/1.92      (![X31 : $i]:
% 1.68/1.92         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 1.68/1.92          | ~ (v1_relat_1 @ X31))),
% 1.68/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.68/1.92  thf('25', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (((k3_xboole_0 @ X0 @ 
% 1.68/1.92            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.68/1.92            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['23', '24'])).
% 1.68/1.92  thf(dt_k7_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.68/1.92  thf('26', plain,
% 1.68/1.92      (![X17 : $i, X18 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 1.68/1.92      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.68/1.92  thf('27', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X1)
% 1.68/1.92          | ((k3_xboole_0 @ X0 @ 
% 1.68/1.92              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.68/1.92              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.68/1.92      inference('clc', [status(thm)], ['25', '26'])).
% 1.68/1.92  thf('28', plain,
% 1.68/1.92      ((((k3_xboole_0 @ sk_A @ 
% 1.68/1.92          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.68/1.92          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.68/1.92      inference('sup+', [status(thm)], ['22', '27'])).
% 1.68/1.92  thf('29', plain,
% 1.68/1.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92         = (k6_relat_1 @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.68/1.92  thf('30', plain,
% 1.68/1.92      (![X34 : $i, X35 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X34)
% 1.68/1.92          | ((k7_relat_1 @ X35 @ (k1_relat_1 @ X34))
% 1.68/1.92              = (k7_relat_1 @ X35 @ 
% 1.68/1.92                 (k1_relat_1 @ (k7_relat_1 @ X34 @ (k1_relat_1 @ X35)))))
% 1.68/1.92          | ~ (v1_relat_1 @ X35))),
% 1.68/1.92      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.68/1.92  thf('31', plain,
% 1.68/1.92      (![X34 : $i, X35 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X34)
% 1.68/1.92          | ((k7_relat_1 @ X35 @ (k1_relat_1 @ X34))
% 1.68/1.92              = (k7_relat_1 @ X35 @ 
% 1.68/1.92                 (k1_relat_1 @ (k7_relat_1 @ X34 @ (k1_relat_1 @ X35)))))
% 1.68/1.92          | ~ (v1_relat_1 @ X35))),
% 1.68/1.92      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.68/1.92  thf('32', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.68/1.92            (k1_relat_1 @ X1))
% 1.68/1.92            = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.68/1.92               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 1.68/1.92          | ~ (v1_relat_1 @ X1))),
% 1.68/1.92      inference('sup+', [status(thm)], ['30', '31'])).
% 1.68/1.92  thf('33', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 1.68/1.92          | ~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.68/1.92              (k1_relat_1 @ X1))
% 1.68/1.92              = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.68/1.92                 (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))))))),
% 1.68/1.92      inference('simplify', [status(thm)], ['32'])).
% 1.68/1.92  thf('34', plain,
% 1.68/1.92      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.68/1.92        | ((k7_relat_1 @ 
% 1.68/1.92            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 1.68/1.92            (k1_relat_1 @ sk_B))
% 1.68/1.92            = (k7_relat_1 @ 
% 1.68/1.92               (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 1.68/1.92               (k1_relat_1 @ 
% 1.68/1.92                (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))))))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_B)
% 1.68/1.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['29', '33'])).
% 1.68/1.92  thf('35', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('36', plain,
% 1.68/1.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92         = (k6_relat_1 @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.68/1.92  thf('37', plain,
% 1.68/1.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92         = (k6_relat_1 @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.68/1.92  thf('38', plain,
% 1.68/1.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.68/1.92         = (k6_relat_1 @ sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.68/1.92  thf('39', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('41', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('42', plain,
% 1.68/1.92      (((k6_relat_1 @ sk_A)
% 1.68/1.92         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 1.68/1.92            (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.68/1.92      inference('demod', [status(thm)],
% 1.68/1.92                ['34', '35', '36', '37', '38', '39', '40', '41'])).
% 1.68/1.92  thf(t87_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ B ) =>
% 1.68/1.92       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.68/1.92  thf('43', plain,
% 1.68/1.92      (![X38 : $i, X39 : $i]:
% 1.68/1.92         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X38 @ X39)) @ X39)
% 1.68/1.92          | ~ (v1_relat_1 @ X38))),
% 1.68/1.92      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.68/1.92  thf('44', plain,
% 1.68/1.92      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 1.68/1.92         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.68/1.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['42', '43'])).
% 1.68/1.92  thf('45', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('46', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('47', plain,
% 1.68/1.92      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.68/1.92      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.68/1.92  thf('48', plain,
% 1.68/1.92      (![X38 : $i, X39 : $i]:
% 1.68/1.92         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X38 @ X39)) @ X39)
% 1.68/1.92          | ~ (v1_relat_1 @ X38))),
% 1.68/1.92      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.68/1.92  thf(d10_xboole_0, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.68/1.92  thf('49', plain,
% 1.68/1.92      (![X0 : $i, X2 : $i]:
% 1.68/1.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.68/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.68/1.92  thf('50', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X1)
% 1.68/1.92          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.68/1.92          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.68/1.92      inference('sup-', [status(thm)], ['48', '49'])).
% 1.68/1.92  thf('51', plain,
% 1.68/1.92      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.68/1.92      inference('sup-', [status(thm)], ['47', '50'])).
% 1.68/1.92  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('53', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.68/1.92      inference('demod', [status(thm)], ['51', '52'])).
% 1.68/1.92  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('55', plain,
% 1.68/1.92      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.68/1.92         = (sk_A))),
% 1.68/1.92      inference('demod', [status(thm)], ['28', '53', '54'])).
% 1.68/1.92  thf(t43_funct_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.68/1.92       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.68/1.92  thf('56', plain,
% 1.68/1.92      (![X46 : $i, X47 : $i]:
% 1.68/1.92         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 1.68/1.92           = (k6_relat_1 @ (k3_xboole_0 @ X46 @ X47)))),
% 1.68/1.92      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.68/1.92  thf(t182_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) =>
% 1.68/1.92       ( ![B:$i]:
% 1.68/1.92         ( ( v1_relat_1 @ B ) =>
% 1.68/1.92           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.68/1.92             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.68/1.92  thf('57', plain,
% 1.68/1.92      (![X32 : $i, X33 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X32)
% 1.68/1.92          | ((k1_relat_1 @ (k5_relat_1 @ X33 @ X32))
% 1.68/1.92              = (k10_relat_1 @ X33 @ (k1_relat_1 @ X32)))
% 1.68/1.92          | ~ (v1_relat_1 @ X33))),
% 1.68/1.92      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.92  thf(t167_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ B ) =>
% 1.68/1.92       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.68/1.92  thf('58', plain,
% 1.68/1.92      (![X29 : $i, X30 : $i]:
% 1.68/1.92         ((r1_tarski @ (k10_relat_1 @ X29 @ X30) @ (k1_relat_1 @ X29))
% 1.68/1.92          | ~ (v1_relat_1 @ X29))),
% 1.68/1.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.68/1.92  thf('59', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.68/1.92           (k1_relat_1 @ X1))
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | ~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X1))),
% 1.68/1.92      inference('sup+', [status(thm)], ['57', '58'])).
% 1.68/1.92  thf('60', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X1)
% 1.68/1.92          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.68/1.92             (k1_relat_1 @ X1)))),
% 1.68/1.92      inference('simplify', [status(thm)], ['59'])).
% 1.68/1.92  thf('61', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.68/1.92           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.68/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.68/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['56', '60'])).
% 1.68/1.92  thf('62', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('63', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 1.68/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.92  thf('64', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('65', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.68/1.92  thf('66', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.68/1.92      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 1.68/1.92  thf('67', plain,
% 1.68/1.92      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['55', '66'])).
% 1.68/1.92  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 1.68/1.92  
% 1.68/1.92  % SZS output end Refutation
% 1.68/1.92  
% 1.68/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
