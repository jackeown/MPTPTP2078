%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4eO6P5AMMu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 9.74s
% Output     : Refutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :  318 (6153 expanded)
%              Number of leaves         :   34 (1845 expanded)
%              Depth                    :   49
%              Number of atoms          : 2712 (69588 expanded)
%              Number of equality atoms :  147 (2312 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k9_relat_1 @ X28 @ ( k3_xboole_0 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X28 @ X29 ) @ ( k9_relat_1 @ X28 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( r1_tarski @ ( k10_relat_1 @ X33 @ ( k9_relat_1 @ X33 @ X34 ) ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('11',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k9_relat_1 @ X35 @ X36 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k9_relat_1 @ X35 @ X36 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','52'])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('59',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k9_relat_1 @ X35 @ X36 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('67',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['23','94'])).

thf('96',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('98',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('104',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('114',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['112','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('130',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k9_relat_1 @ X35 @ X36 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('133',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('138',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
        = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['136','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('150',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153'])).

thf('155',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('158',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('159',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k10_relat_1 @ X37 @ X38 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X37 ) @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('160',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('172',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('188',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('189',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k9_relat_1 @ X35 @ X36 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('191',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','193'])).

thf('195',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['187','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['186','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','208'])).

thf('210',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','154','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','124','125','126','127'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k10_relat_1 @ X37 @ X38 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X37 ) @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('232',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('233',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('234',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ ( k1_relat_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['231','241'])).

thf('243',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('244',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('245',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['243','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['242','249','250','251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['230','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','258'])).

thf('260',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('263',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['18','262'])).

thf('264',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('265',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['18','262'])).

thf('266',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['17','263','264','265'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('267',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('268',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('270',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('275',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['273','276'])).

thf('278',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['268','277'])).

thf('279',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('280',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,(
    $false ),
    inference(demod,[status(thm)],['0','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4eO6P5AMMu
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 9.74/9.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.74/9.99  % Solved by: fo/fo7.sh
% 9.74/9.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.74/9.99  % done 13141 iterations in 9.540s
% 9.74/9.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.74/9.99  % SZS output start Refutation
% 9.74/9.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.74/9.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 9.74/9.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 9.74/9.99  thf(sk_C_type, type, sk_C: $i).
% 9.74/9.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.74/9.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.74/9.99  thf(sk_B_type, type, sk_B: $i).
% 9.74/9.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.74/9.99  thf(sk_A_type, type, sk_A: $i).
% 9.74/9.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.74/9.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.74/9.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.74/9.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.74/9.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.74/9.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.74/9.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.74/9.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.74/9.99  thf(t157_funct_1, conjecture,
% 9.74/9.99    (![A:$i,B:$i,C:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.74/9.99       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 9.74/9.99           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 9.74/9.99         ( r1_tarski @ A @ B ) ) ))).
% 9.74/9.99  thf(zf_stmt_0, negated_conjecture,
% 9.74/9.99    (~( ![A:$i,B:$i,C:$i]:
% 9.74/9.99        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.74/9.99          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 9.74/9.99              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 9.74/9.99            ( r1_tarski @ A @ B ) ) ) )),
% 9.74/9.99    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 9.74/9.99  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf(t121_funct_1, axiom,
% 9.74/9.99    (![A:$i,B:$i,C:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.74/9.99       ( ( v2_funct_1 @ C ) =>
% 9.74/9.99         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 9.74/9.99           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 9.74/9.99  thf('1', plain,
% 9.74/9.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X28)
% 9.74/9.99          | ((k9_relat_1 @ X28 @ (k3_xboole_0 @ X29 @ X30))
% 9.74/9.99              = (k3_xboole_0 @ (k9_relat_1 @ X28 @ X29) @ 
% 9.74/9.99                 (k9_relat_1 @ X28 @ X30)))
% 9.74/9.99          | ~ (v1_funct_1 @ X28)
% 9.74/9.99          | ~ (v1_relat_1 @ X28))),
% 9.74/9.99      inference('cnf', [status(esa)], [t121_funct_1])).
% 9.74/9.99  thf('2', plain,
% 9.74/9.99      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf(t28_xboole_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.74/9.99  thf('3', plain,
% 9.74/9.99      (![X15 : $i, X16 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/9.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/9.99  thf('4', plain,
% 9.74/9.99      (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 9.74/9.99         = (k9_relat_1 @ sk_C @ sk_A))),
% 9.74/9.99      inference('sup-', [status(thm)], ['2', '3'])).
% 9.74/9.99  thf('5', plain,
% 9.74/9.99      ((((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 9.74/9.99          = (k9_relat_1 @ sk_C @ sk_A))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['1', '4'])).
% 9.74/9.99  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('9', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 9.74/9.99         = (k9_relat_1 @ sk_C @ sk_A))),
% 9.74/9.99      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 9.74/9.99  thf(t152_funct_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.74/9.99       ( ( v2_funct_1 @ B ) =>
% 9.74/9.99         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 9.74/9.99  thf('10', plain,
% 9.74/9.99      (![X33 : $i, X34 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X33)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ X33 @ (k9_relat_1 @ X33 @ X34)) @ X34)
% 9.74/9.99          | ~ (v1_funct_1 @ X33)
% 9.74/9.99          | ~ (v1_relat_1 @ X33))),
% 9.74/9.99      inference('cnf', [status(esa)], [t152_funct_1])).
% 9.74/9.99  thf('11', plain,
% 9.74/9.99      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 9.74/9.99         (k3_xboole_0 @ sk_A @ sk_B))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['9', '10'])).
% 9.74/9.99  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('15', plain,
% 9.74/9.99      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 9.74/9.99        (k3_xboole_0 @ sk_A @ sk_B))),
% 9.74/9.99      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 9.74/9.99  thf(d10_xboole_0, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.74/9.99  thf('16', plain,
% 9.74/9.99      (![X0 : $i, X2 : $i]:
% 9.74/9.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.74/9.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.74/9.99  thf('17', plain,
% 9.74/9.99      ((~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 9.74/9.99           (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 9.74/9.99        | ((k3_xboole_0 @ sk_A @ sk_B)
% 9.74/9.99            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['15', '16'])).
% 9.74/9.99  thf('18', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf(dt_k2_funct_1, axiom,
% 9.74/9.99    (![A:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.74/9.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 9.74/9.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 9.74/9.99  thf('19', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_funct_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('20', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('21', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('22', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_funct_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf(t154_funct_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.74/9.99       ( ( v2_funct_1 @ B ) =>
% 9.74/9.99         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 9.74/9.99  thf('23', plain,
% 9.74/9.99      (![X35 : $i, X36 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X35)
% 9.74/9.99          | ((k9_relat_1 @ X35 @ X36)
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 9.74/9.99          | ~ (v1_funct_1 @ X35)
% 9.74/9.99          | ~ (v1_relat_1 @ X35))),
% 9.74/9.99      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.74/9.99  thf('24', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('25', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf(t144_relat_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( v1_relat_1 @ B ) =>
% 9.74/9.99       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 9.74/9.99  thf('26', plain,
% 9.74/9.99      (![X22 : $i, X23 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/9.99          | ~ (v1_relat_1 @ X22))),
% 9.74/9.99      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/9.99  thf('27', plain,
% 9.74/9.99      (![X35 : $i, X36 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X35)
% 9.74/9.99          | ((k9_relat_1 @ X35 @ X36)
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 9.74/9.99          | ~ (v1_funct_1 @ X35)
% 9.74/9.99          | ~ (v1_relat_1 @ X35))),
% 9.74/9.99      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.74/9.99  thf(t169_relat_1, axiom,
% 9.74/9.99    (![A:$i]:
% 9.74/9.99     ( ( v1_relat_1 @ A ) =>
% 9.74/9.99       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 9.74/9.99  thf('28', plain,
% 9.74/9.99      (![X24 : $i]:
% 9.74/9.99         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 9.74/9.99          | ~ (v1_relat_1 @ X24))),
% 9.74/9.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.74/9.99  thf(t170_relat_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( v1_relat_1 @ B ) =>
% 9.74/9.99       ( r1_tarski @
% 9.74/9.99         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 9.74/9.99  thf('29', plain,
% 9.74/9.99      (![X25 : $i, X26 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ 
% 9.74/9.99           (k10_relat_1 @ X25 @ (k2_relat_1 @ X25)))
% 9.74/9.99          | ~ (v1_relat_1 @ X25))),
% 9.74/9.99      inference('cnf', [status(esa)], [t170_relat_1])).
% 9.74/9.99  thf('30', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 9.74/9.99           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('sup+', [status(thm)], ['28', '29'])).
% 9.74/9.99  thf('31', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 9.74/9.99             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 9.74/9.99      inference('simplify', [status(thm)], ['30'])).
% 9.74/9.99  thf(t12_xboole_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 9.74/9.99  thf('32', plain,
% 9.74/9.99      (![X11 : $i, X12 : $i]:
% 9.74/9.99         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 9.74/9.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.74/9.99  thf('33', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ((k2_xboole_0 @ (k1_relat_1 @ X0) @ 
% 9.74/9.99              (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['31', '32'])).
% 9.74/9.99  thf(t11_xboole_1, axiom,
% 9.74/9.99    (![A:$i,B:$i,C:$i]:
% 9.74/9.99     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 9.74/9.99  thf('34', plain,
% 9.74/9.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.74/9.99         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.74/9.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.74/9.99  thf('35', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 9.74/9.99      inference('sup-', [status(thm)], ['33', '34'])).
% 9.74/9.99  thf('36', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (r1_tarski @ 
% 9.74/9.99             (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['27', '35'])).
% 9.74/9.99  thf('37', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['26', '36'])).
% 9.74/9.99  thf('38', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['37'])).
% 9.74/9.99  thf('39', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['25', '38'])).
% 9.74/9.99  thf('40', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['39'])).
% 9.74/9.99  thf('41', plain,
% 9.74/9.99      (![X24 : $i]:
% 9.74/9.99         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 9.74/9.99          | ~ (v1_relat_1 @ X24))),
% 9.74/9.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.74/9.99  thf('42', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 9.74/9.99             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 9.74/9.99      inference('simplify', [status(thm)], ['30'])).
% 9.74/9.99  thf('43', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('44', plain,
% 9.74/9.99      (![X11 : $i, X12 : $i]:
% 9.74/9.99         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 9.74/9.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.74/9.99  thf('45', plain,
% 9.74/9.99      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup-', [status(thm)], ['43', '44'])).
% 9.74/9.99  thf('46', plain,
% 9.74/9.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.74/9.99         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.74/9.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.74/9.99  thf('47', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['45', '46'])).
% 9.74/9.99  thf('48', plain,
% 9.74/9.99      ((~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['42', '47'])).
% 9.74/9.99  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('50', plain,
% 9.74/9.99      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['48', '49'])).
% 9.74/9.99  thf('51', plain,
% 9.74/9.99      (![X11 : $i, X12 : $i]:
% 9.74/9.99         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 9.74/9.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.74/9.99  thf('52', plain,
% 9.74/9.99      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 9.74/9.99         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['50', '51'])).
% 9.74/9.99  thf('53', plain,
% 9.74/9.99      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C))
% 9.74/9.99          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['41', '52'])).
% 9.74/9.99  thf('54', plain,
% 9.74/9.99      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup-', [status(thm)], ['43', '44'])).
% 9.74/9.99  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('56', plain,
% 9.74/9.99      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.74/9.99  thf('57', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.74/9.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.74/9.99  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.74/9.99      inference('simplify', [status(thm)], ['57'])).
% 9.74/9.99  thf(t147_funct_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.74/9.99       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 9.74/9.99         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 9.74/9.99  thf('59', plain,
% 9.74/9.99      (![X31 : $i, X32 : $i]:
% 9.74/9.99         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 9.74/9.99          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 9.74/9.99          | ~ (v1_funct_1 @ X32)
% 9.74/9.99          | ~ (v1_relat_1 @ X32))),
% 9.74/9.99      inference('cnf', [status(esa)], [t147_funct_1])).
% 9.74/9.99  thf('60', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99              = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['58', '59'])).
% 9.74/9.99  thf('61', plain,
% 9.74/9.99      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['56', '60'])).
% 9.74/9.99  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('64', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.74/9.99  thf('65', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('66', plain,
% 9.74/9.99      (![X35 : $i, X36 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X35)
% 9.74/9.99          | ((k9_relat_1 @ X35 @ X36)
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 9.74/9.99          | ~ (v1_funct_1 @ X35)
% 9.74/9.99          | ~ (v1_relat_1 @ X35))),
% 9.74/9.99      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.74/9.99  thf('67', plain,
% 9.74/9.99      (![X24 : $i]:
% 9.74/9.99         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 9.74/9.99          | ~ (v1_relat_1 @ X24))),
% 9.74/9.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.74/9.99  thf('68', plain,
% 9.74/9.99      (![X25 : $i, X26 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ 
% 9.74/9.99           (k10_relat_1 @ X25 @ (k2_relat_1 @ X25)))
% 9.74/9.99          | ~ (v1_relat_1 @ X25))),
% 9.74/9.99      inference('cnf', [status(esa)], [t170_relat_1])).
% 9.74/9.99  thf('69', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('sup+', [status(thm)], ['67', '68'])).
% 9.74/9.99  thf('70', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 9.74/9.99      inference('simplify', [status(thm)], ['69'])).
% 9.74/9.99  thf('71', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 9.74/9.99          | ~ (v1_relat_1 @ X1)
% 9.74/9.99          | ~ (v1_funct_1 @ X1)
% 9.74/9.99          | ~ (v2_funct_1 @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 9.74/9.99      inference('sup+', [status(thm)], ['66', '70'])).
% 9.74/9.99  thf('72', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 9.74/9.99             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['65', '71'])).
% 9.74/9.99  thf('73', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['72'])).
% 9.74/9.99  thf('74', plain,
% 9.74/9.99      (![X0 : $i, X2 : $i]:
% 9.74/9.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.74/9.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.74/9.99  thf('75', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 9.74/9.99               (k9_relat_1 @ X0 @ X1))
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['73', '74'])).
% 9.74/9.99  thf('76', plain,
% 9.74/9.99      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_relat_1 @ sk_C))
% 9.74/9.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99            = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup-', [status(thm)], ['64', '75'])).
% 9.74/9.99  thf('77', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.74/9.99  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('81', plain,
% 9.74/9.99      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_relat_1 @ sk_C))
% 9.74/9.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 9.74/9.99  thf('82', plain,
% 9.74/9.99      ((~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C)
% 9.74/9.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['40', '81'])).
% 9.74/9.99  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('86', plain,
% 9.74/9.99      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 9.74/9.99  thf('87', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 9.74/9.99      inference('simplify', [status(thm)], ['69'])).
% 9.74/9.99  thf('88', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/9.99           (k2_relat_1 @ sk_C))
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/9.99      inference('sup+', [status(thm)], ['86', '87'])).
% 9.74/9.99  thf('89', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ sk_C)
% 9.74/9.99          | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/9.99             (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['24', '88'])).
% 9.74/9.99  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('92', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/9.99          (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['89', '90', '91'])).
% 9.74/9.99  thf('93', plain,
% 9.74/9.99      (![X15 : $i, X16 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/9.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/9.99  thf('94', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k3_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/9.99           (k2_relat_1 @ sk_C)) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['92', '93'])).
% 9.74/9.99  thf('95', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 9.74/9.99            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99          | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99          | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['23', '94'])).
% 9.74/9.99  thf('96', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.74/9.99  thf('97', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['72'])).
% 9.74/9.99  thf('98', plain,
% 9.74/9.99      (((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['96', '97'])).
% 9.74/9.99  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('102', plain,
% 9.74/9.99      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 9.74/9.99  thf('103', plain,
% 9.74/9.99      (![X22 : $i, X23 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/9.99          | ~ (v1_relat_1 @ X22))),
% 9.74/9.99      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/9.99  thf('104', plain,
% 9.74/9.99      (![X11 : $i, X12 : $i]:
% 9.74/9.99         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 9.74/9.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.74/9.99  thf('105', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 9.74/9.99              = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['103', '104'])).
% 9.74/9.99  thf('106', plain,
% 9.74/9.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.74/9.99         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.74/9.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.74/9.99  thf('107', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ X1))),
% 9.74/9.99      inference('sup-', [status(thm)], ['105', '106'])).
% 9.74/9.99  thf('108', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99          | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup-', [status(thm)], ['102', '107'])).
% 9.74/9.99  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('110', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99          (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['108', '109'])).
% 9.74/9.99  thf('111', plain,
% 9.74/9.99      (![X15 : $i, X16 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/9.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/9.99  thf('112', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ sk_C))) = (k9_relat_1 @ sk_C @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['110', '111'])).
% 9.74/9.99  thf('113', plain,
% 9.74/9.99      (![X22 : $i, X23 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/9.99          | ~ (v1_relat_1 @ X22))),
% 9.74/9.99      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/9.99  thf(t17_xboole_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 9.74/9.99  thf('114', plain,
% 9.74/9.99      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 9.74/9.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.74/9.99  thf('115', plain,
% 9.74/9.99      (![X11 : $i, X12 : $i]:
% 9.74/9.99         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 9.74/9.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.74/9.99  thf('116', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['114', '115'])).
% 9.74/9.99  thf('117', plain,
% 9.74/9.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.74/9.99         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.74/9.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.74/9.99  thf('118', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.74/9.99         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 9.74/9.99      inference('sup-', [status(thm)], ['116', '117'])).
% 9.74/9.99  thf('119', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k3_xboole_0 @ (k9_relat_1 @ X0 @ X1) @ X2) @ 
% 9.74/9.99             (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['113', '118'])).
% 9.74/9.99  thf('120', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 9.74/9.99          | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['112', '119'])).
% 9.74/9.99  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('122', plain,
% 9.74/9.99      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['120', '121'])).
% 9.74/9.99  thf('123', plain,
% 9.74/9.99      (![X15 : $i, X16 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/9.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/9.99  thf('124', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 9.74/9.99           = (k9_relat_1 @ sk_C @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['122', '123'])).
% 9.74/9.99  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('128', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 9.74/9.99      inference('demod', [status(thm)], ['95', '124', '125', '126', '127'])).
% 9.74/9.99  thf('129', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99              = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['58', '59'])).
% 9.74/9.99  thf('130', plain,
% 9.74/9.99      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 9.74/9.99          (k9_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 9.74/9.99          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/9.99      inference('sup+', [status(thm)], ['128', '129'])).
% 9.74/9.99  thf('131', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('132', plain,
% 9.74/9.99      (![X35 : $i, X36 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X35)
% 9.74/9.99          | ((k9_relat_1 @ X35 @ X36)
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 9.74/9.99          | ~ (v1_funct_1 @ X35)
% 9.74/9.99          | ~ (v1_relat_1 @ X35))),
% 9.74/9.99      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.74/9.99  thf('133', plain,
% 9.74/9.99      (![X24 : $i]:
% 9.74/9.99         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 9.74/9.99          | ~ (v1_relat_1 @ X24))),
% 9.74/9.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.74/9.99  thf('134', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 9.74/9.99      inference('sup+', [status(thm)], ['132', '133'])).
% 9.74/9.99  thf('135', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['131', '134'])).
% 9.74/9.99  thf('136', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['135'])).
% 9.74/9.99  thf('137', plain,
% 9.74/9.99      (![X22 : $i, X23 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/9.99          | ~ (v1_relat_1 @ X22))),
% 9.74/9.99      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/9.99  thf('138', plain,
% 9.74/9.99      (![X31 : $i, X32 : $i]:
% 9.74/9.99         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 9.74/9.99          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 9.74/9.99          | ~ (v1_funct_1 @ X32)
% 9.74/9.99          | ~ (v1_relat_1 @ X32))),
% 9.74/9.99      inference('cnf', [status(esa)], [t147_funct_1])).
% 9.74/9.99  thf('139', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 9.74/9.99              = (k9_relat_1 @ X0 @ X1)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['137', '138'])).
% 9.74/9.99  thf('140', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 9.74/9.99            = (k9_relat_1 @ X0 @ X1))
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['139'])).
% 9.74/9.99  thf('141', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ sk_C))) = (k9_relat_1 @ sk_C @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['110', '111'])).
% 9.74/9.99  thf('142', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99            (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99            = (k9_relat_1 @ sk_C @ 
% 9.74/9.99               (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0))))
% 9.74/9.99          | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99          | ~ (v1_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['140', '141'])).
% 9.74/9.99  thf('143', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k3_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ sk_C))) = (k9_relat_1 @ sk_C @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['110', '111'])).
% 9.74/9.99  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('146', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((k9_relat_1 @ sk_C @ X0)
% 9.74/9.99           = (k9_relat_1 @ sk_C @ 
% 9.74/9.99              (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0))))),
% 9.74/9.99      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 9.74/9.99  thf('147', plain,
% 9.74/9.99      ((((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99          = (k9_relat_1 @ sk_C @ 
% 9.74/9.99             (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['136', '146'])).
% 9.74/9.99  thf('148', plain,
% 9.74/9.99      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 9.74/9.99  thf('149', plain,
% 9.74/9.99      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.74/9.99  thf('150', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.74/9.99  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('154', plain,
% 9.74/9.99      (((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99         = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)],
% 9.74/9.99                ['147', '148', '149', '150', '151', '152', '153'])).
% 9.74/9.99  thf('155', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_funct_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('156', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('157', plain,
% 9.74/9.99      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.74/9.99  thf('158', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf(t155_funct_1, axiom,
% 9.74/9.99    (![A:$i,B:$i]:
% 9.74/9.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.74/9.99       ( ( v2_funct_1 @ B ) =>
% 9.74/9.99         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 9.74/9.99  thf('159', plain,
% 9.74/9.99      (![X37 : $i, X38 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X37)
% 9.74/9.99          | ((k10_relat_1 @ X37 @ X38)
% 9.74/9.99              = (k9_relat_1 @ (k2_funct_1 @ X37) @ X38))
% 9.74/9.99          | ~ (v1_funct_1 @ X37)
% 9.74/9.99          | ~ (v1_relat_1 @ X37))),
% 9.74/9.99      inference('cnf', [status(esa)], [t155_funct_1])).
% 9.74/9.99  thf('160', plain,
% 9.74/9.99      (![X22 : $i, X23 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/9.99          | ~ (v1_relat_1 @ X22))),
% 9.74/9.99      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/9.99  thf('161', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 9.74/9.99           (k2_relat_1 @ (k2_funct_1 @ X1)))
% 9.74/9.99          | ~ (v1_relat_1 @ X1)
% 9.74/9.99          | ~ (v1_funct_1 @ X1)
% 9.74/9.99          | ~ (v2_funct_1 @ X1)
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 9.74/9.99      inference('sup+', [status(thm)], ['159', '160'])).
% 9.74/9.99  thf('162', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 9.74/9.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 9.74/9.99      inference('sup-', [status(thm)], ['158', '161'])).
% 9.74/9.99  thf('163', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 9.74/9.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['162'])).
% 9.74/9.99  thf('164', plain,
% 9.74/9.99      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/9.99        | ~ (v1_relat_1 @ sk_C)
% 9.74/9.99        | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99        | ~ (v2_funct_1 @ sk_C))),
% 9.74/9.99      inference('sup+', [status(thm)], ['157', '163'])).
% 9.74/9.99  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('168', plain,
% 9.74/9.99      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/9.99      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 9.74/9.99  thf('169', plain,
% 9.74/9.99      (![X31 : $i, X32 : $i]:
% 9.74/9.99         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 9.74/9.99          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 9.74/9.99          | ~ (v1_funct_1 @ X32)
% 9.74/9.99          | ~ (v1_relat_1 @ X32))),
% 9.74/9.99      inference('cnf', [status(esa)], [t147_funct_1])).
% 9.74/9.99  thf('170', plain,
% 9.74/9.99      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 9.74/9.99            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 9.74/9.99            = (k1_relat_1 @ sk_C)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['168', '169'])).
% 9.74/9.99  thf('171', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['39'])).
% 9.74/9.99  thf('172', plain,
% 9.74/9.99      (![X24 : $i]:
% 9.74/9.99         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 9.74/9.99          | ~ (v1_relat_1 @ X24))),
% 9.74/9.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.74/9.99  thf('173', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99              = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['58', '59'])).
% 9.74/9.99  thf('174', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('sup+', [status(thm)], ['172', '173'])).
% 9.74/9.99  thf('175', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('simplify', [status(thm)], ['174'])).
% 9.74/9.99  thf('176', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 9.74/9.99               (k9_relat_1 @ X0 @ X1))
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['73', '74'])).
% 9.74/9.99  thf('177', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['175', '176'])).
% 9.74/9.99  thf('178', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X0)
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('simplify', [status(thm)], ['177'])).
% 9.74/9.99  thf('179', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0))),
% 9.74/9.99      inference('sup-', [status(thm)], ['171', '178'])).
% 9.74/9.99  thf('180', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 9.74/9.99            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['179'])).
% 9.74/9.99  thf('181', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 9.74/9.99              = (k2_relat_1 @ X0)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['58', '59'])).
% 9.74/9.99  thf('182', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 9.74/9.99           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0))),
% 9.74/9.99      inference('simplify', [status(thm)], ['72'])).
% 9.74/9.99  thf('183', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0))),
% 9.74/9.99      inference('sup+', [status(thm)], ['181', '182'])).
% 9.74/9.99  thf('184', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 9.74/9.99      inference('simplify', [status(thm)], ['183'])).
% 9.74/9.99  thf('185', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 9.74/9.99           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (v2_funct_1 @ X0))),
% 9.74/9.99      inference('sup+', [status(thm)], ['180', '184'])).
% 9.74/9.99  thf('186', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_funct_1 @ X0)
% 9.74/9.99          | ~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 9.74/9.99             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 9.74/9.99      inference('simplify', [status(thm)], ['185'])).
% 9.74/9.99  thf('187', plain,
% 9.74/9.99      (![X27 : $i]:
% 9.74/9.99         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/9.99          | ~ (v1_funct_1 @ X27)
% 9.74/9.99          | ~ (v1_relat_1 @ X27))),
% 9.74/9.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/9.99  thf('188', plain,
% 9.74/9.99      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 9.74/9.99  thf('189', plain,
% 9.74/9.99      (![X35 : $i, X36 : $i]:
% 9.74/9.99         (~ (v2_funct_1 @ X35)
% 9.74/9.99          | ((k9_relat_1 @ X35 @ X36)
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 9.74/9.99          | ~ (v1_funct_1 @ X35)
% 9.74/9.99          | ~ (v1_relat_1 @ X35))),
% 9.74/9.99      inference('cnf', [status(esa)], [t154_funct_1])).
% 9.74/9.99  thf('190', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 9.74/9.99      inference('simplify', [status(thm)], ['69'])).
% 9.74/9.99  thf('191', plain,
% 9.74/9.99      (![X0 : $i, X2 : $i]:
% 9.74/9.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.74/9.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.74/9.99  thf('192', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (v1_relat_1 @ X0)
% 9.74/9.99          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 9.74/9.99          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['190', '191'])).
% 9.74/9.99  thf('193', plain,
% 9.74/9.99      (![X0 : $i, X1 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X1)) @ 
% 9.74/9.99             (k9_relat_1 @ X1 @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ X1)
% 9.74/9.99          | ~ (v1_funct_1 @ X1)
% 9.74/9.99          | ~ (v2_funct_1 @ X1)
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ X1))
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 9.74/9.99      inference('sup-', [status(thm)], ['189', '192'])).
% 9.74/9.99  thf('194', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99          | ((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99              = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 9.74/9.99          | ~ (v2_funct_1 @ sk_C)
% 9.74/9.99          | ~ (v1_funct_1 @ sk_C)
% 9.74/9.99          | ~ (v1_relat_1 @ sk_C))),
% 9.74/9.99      inference('sup-', [status(thm)], ['188', '193'])).
% 9.74/9.99  thf('195', plain,
% 9.74/9.99      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 9.74/9.99      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 9.74/9.99  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 9.74/9.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.99  thf('199', plain,
% 9.74/9.99      (![X0 : $i]:
% 9.74/9.99         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0))
% 9.74/9.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/9.99          | ((k2_relat_1 @ sk_C) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))),
% 9.74/9.99      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 9.74/10.00  thf('200', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (v1_relat_1 @ sk_C)
% 9.74/10.00          | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00          | ((k2_relat_1 @ sk_C) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 9.74/10.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['187', '199'])).
% 9.74/10.00  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('203', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (((k2_relat_1 @ sk_C) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 9.74/10.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)))),
% 9.74/10.00      inference('demod', [status(thm)], ['200', '201', '202'])).
% 9.74/10.00  thf('204', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ sk_C)
% 9.74/10.00        | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00        | ~ (v2_funct_1 @ sk_C)
% 9.74/10.00        | ((k2_relat_1 @ sk_C)
% 9.74/10.00            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 9.74/10.00      inference('sup-', [status(thm)], ['186', '203'])).
% 9.74/10.00  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('208', plain,
% 9.74/10.00      (((k2_relat_1 @ sk_C)
% 9.74/10.00         = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 9.74/10.00  thf('209', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 9.74/10.00            = (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['170', '208'])).
% 9.74/10.00  thf('210', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ sk_C)
% 9.74/10.00        | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 9.74/10.00            = (k1_relat_1 @ sk_C))
% 9.74/10.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['156', '209'])).
% 9.74/10.00  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('213', plain,
% 9.74/10.00      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 9.74/10.00          = (k1_relat_1 @ sk_C))
% 9.74/10.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['210', '211', '212'])).
% 9.74/10.00  thf('214', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ sk_C)
% 9.74/10.00        | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 9.74/10.00            = (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['155', '213'])).
% 9.74/10.00  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('217', plain,
% 9.74/10.00      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 9.74/10.00         = (k1_relat_1 @ sk_C))),
% 9.74/10.00      inference('demod', [status(thm)], ['214', '215', '216'])).
% 9.74/10.00  thf('218', plain,
% 9.74/10.00      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 9.74/10.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['130', '154', '217'])).
% 9.74/10.00  thf('219', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ sk_C)
% 9.74/10.00        | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 9.74/10.00      inference('sup-', [status(thm)], ['22', '218'])).
% 9.74/10.00  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('222', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 9.74/10.00      inference('demod', [status(thm)], ['219', '220', '221'])).
% 9.74/10.00  thf('223', plain,
% 9.74/10.00      ((~ (v1_relat_1 @ sk_C)
% 9.74/10.00        | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 9.74/10.00      inference('sup-', [status(thm)], ['21', '222'])).
% 9.74/10.00  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('226', plain,
% 9.74/10.00      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['223', '224', '225'])).
% 9.74/10.00  thf('227', plain,
% 9.74/10.00      (![X31 : $i, X32 : $i]:
% 9.74/10.00         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 9.74/10.00          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 9.74/10.00          | ~ (v1_funct_1 @ X32)
% 9.74/10.00          | ~ (v1_relat_1 @ X32))),
% 9.74/10.00      inference('cnf', [status(esa)], [t147_funct_1])).
% 9.74/10.00  thf('228', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 9.74/10.00          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 9.74/10.00              (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) = (X0)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['226', '227'])).
% 9.74/10.00  thf('229', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 9.74/10.00      inference('demod', [status(thm)], ['95', '124', '125', '126', '127'])).
% 9.74/10.00  thf('230', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 9.74/10.00          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0))
% 9.74/10.00              = (X0)))),
% 9.74/10.00      inference('demod', [status(thm)], ['228', '229'])).
% 9.74/10.00  thf('231', plain,
% 9.74/10.00      (![X37 : $i, X38 : $i]:
% 9.74/10.00         (~ (v2_funct_1 @ X37)
% 9.74/10.00          | ((k10_relat_1 @ X37 @ X38)
% 9.74/10.00              = (k9_relat_1 @ (k2_funct_1 @ X37) @ X38))
% 9.74/10.00          | ~ (v1_funct_1 @ X37)
% 9.74/10.00          | ~ (v1_relat_1 @ X37))),
% 9.74/10.00      inference('cnf', [status(esa)], [t155_funct_1])).
% 9.74/10.00  thf('232', plain,
% 9.74/10.00      (![X27 : $i]:
% 9.74/10.00         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 9.74/10.00          | ~ (v1_funct_1 @ X27)
% 9.74/10.00          | ~ (v1_relat_1 @ X27))),
% 9.74/10.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 9.74/10.00  thf('233', plain,
% 9.74/10.00      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['223', '224', '225'])).
% 9.74/10.00  thf('234', plain,
% 9.74/10.00      (![X22 : $i, X23 : $i]:
% 9.74/10.00         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 9.74/10.00          | ~ (v1_relat_1 @ X22))),
% 9.74/10.00      inference('cnf', [status(esa)], [t144_relat_1])).
% 9.74/10.00  thf('235', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         ((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/10.00           (k1_relat_1 @ sk_C))
% 9.74/10.00          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 9.74/10.00      inference('sup+', [status(thm)], ['233', '234'])).
% 9.74/10.00  thf('236', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (v1_relat_1 @ sk_C)
% 9.74/10.00          | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/10.00             (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['232', '235'])).
% 9.74/10.00  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('239', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/10.00          (k1_relat_1 @ sk_C))),
% 9.74/10.00      inference('demod', [status(thm)], ['236', '237', '238'])).
% 9.74/10.00  thf('240', plain,
% 9.74/10.00      (![X15 : $i, X16 : $i]:
% 9.74/10.00         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/10.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/10.00  thf('241', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         ((k3_xboole_0 @ (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ 
% 9.74/10.00           (k1_relat_1 @ sk_C)) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 9.74/10.00      inference('sup-', [status(thm)], ['239', '240'])).
% 9.74/10.00  thf('242', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ (k1_relat_1 @ sk_C))
% 9.74/10.00            = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 9.74/10.00          | ~ (v1_relat_1 @ sk_C)
% 9.74/10.00          | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00          | ~ (v2_funct_1 @ sk_C))),
% 9.74/10.00      inference('sup+', [status(thm)], ['231', '241'])).
% 9.74/10.00  thf('243', plain,
% 9.74/10.00      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.74/10.00  thf('244', plain,
% 9.74/10.00      (![X25 : $i, X26 : $i]:
% 9.74/10.00         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ 
% 9.74/10.00           (k10_relat_1 @ X25 @ (k2_relat_1 @ X25)))
% 9.74/10.00          | ~ (v1_relat_1 @ X25))),
% 9.74/10.00      inference('cnf', [status(esa)], [t170_relat_1])).
% 9.74/10.00  thf('245', plain,
% 9.74/10.00      (![X15 : $i, X16 : $i]:
% 9.74/10.00         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/10.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/10.00  thf('246', plain,
% 9.74/10.00      (![X0 : $i, X1 : $i]:
% 9.74/10.00         (~ (v1_relat_1 @ X0)
% 9.74/10.00          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ 
% 9.74/10.00              (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) = (k10_relat_1 @ X0 @ X1)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['244', '245'])).
% 9.74/10.00  thf('247', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ (k1_relat_1 @ sk_C))
% 9.74/10.00            = (k10_relat_1 @ sk_C @ X0))
% 9.74/10.00          | ~ (v1_relat_1 @ sk_C))),
% 9.74/10.00      inference('sup+', [status(thm)], ['243', '246'])).
% 9.74/10.00  thf('248', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('249', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         ((k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ (k1_relat_1 @ sk_C))
% 9.74/10.00           = (k10_relat_1 @ sk_C @ X0))),
% 9.74/10.00      inference('demod', [status(thm)], ['247', '248'])).
% 9.74/10.00  thf('250', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('252', plain, ((v2_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('253', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         ((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 9.74/10.00      inference('demod', [status(thm)], ['242', '249', '250', '251', '252'])).
% 9.74/10.00  thf('254', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 9.74/10.00          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 9.74/10.00      inference('demod', [status(thm)], ['230', '253'])).
% 9.74/10.00  thf('255', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (v1_relat_1 @ sk_C)
% 9.74/10.00          | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 9.74/10.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['20', '254'])).
% 9.74/10.00  thf('256', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('257', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('258', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 9.74/10.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 9.74/10.00          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C)))),
% 9.74/10.00      inference('demod', [status(thm)], ['255', '256', '257'])).
% 9.74/10.00  thf('259', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (v1_relat_1 @ sk_C)
% 9.74/10.00          | ~ (v1_funct_1 @ sk_C)
% 9.74/10.00          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 9.74/10.00          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 9.74/10.00      inference('sup-', [status(thm)], ['19', '258'])).
% 9.74/10.00  thf('260', plain, ((v1_relat_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('261', plain, ((v1_funct_1 @ sk_C)),
% 9.74/10.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/10.00  thf('262', plain,
% 9.74/10.00      (![X0 : $i]:
% 9.74/10.00         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 9.74/10.00          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 9.74/10.00      inference('demod', [status(thm)], ['259', '260', '261'])).
% 9.74/10.00  thf('263', plain,
% 9.74/10.00      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 9.74/10.00      inference('sup-', [status(thm)], ['18', '262'])).
% 9.74/10.00  thf('264', plain,
% 9.74/10.00      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 9.74/10.00      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.74/10.00  thf('265', plain,
% 9.74/10.00      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 9.74/10.00      inference('sup-', [status(thm)], ['18', '262'])).
% 9.74/10.00  thf('266', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 9.74/10.00      inference('demod', [status(thm)], ['17', '263', '264', '265'])).
% 9.74/10.00  thf(t100_xboole_1, axiom,
% 9.74/10.00    (![A:$i,B:$i]:
% 9.74/10.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.74/10.00  thf('267', plain,
% 9.74/10.00      (![X6 : $i, X7 : $i]:
% 9.74/10.00         ((k4_xboole_0 @ X6 @ X7)
% 9.74/10.00           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 9.74/10.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.74/10.00  thf('268', plain,
% 9.74/10.00      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 9.74/10.00      inference('sup+', [status(thm)], ['266', '267'])).
% 9.74/10.00  thf('269', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.74/10.00      inference('simplify', [status(thm)], ['57'])).
% 9.74/10.00  thf('270', plain,
% 9.74/10.00      (![X15 : $i, X16 : $i]:
% 9.74/10.00         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 9.74/10.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.74/10.00  thf('271', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 9.74/10.00      inference('sup-', [status(thm)], ['269', '270'])).
% 9.74/10.00  thf('272', plain,
% 9.74/10.00      (![X6 : $i, X7 : $i]:
% 9.74/10.00         ((k4_xboole_0 @ X6 @ X7)
% 9.74/10.00           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 9.74/10.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.74/10.00  thf('273', plain,
% 9.74/10.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.74/10.00      inference('sup+', [status(thm)], ['271', '272'])).
% 9.74/10.00  thf('274', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.74/10.00      inference('simplify', [status(thm)], ['57'])).
% 9.74/10.00  thf(l32_xboole_1, axiom,
% 9.74/10.00    (![A:$i,B:$i]:
% 9.74/10.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.74/10.00  thf('275', plain,
% 9.74/10.00      (![X3 : $i, X5 : $i]:
% 9.74/10.00         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 9.74/10.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.74/10.00  thf('276', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.74/10.00      inference('sup-', [status(thm)], ['274', '275'])).
% 9.74/10.00  thf('277', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.74/10.00      inference('sup+', [status(thm)], ['273', '276'])).
% 9.74/10.00  thf('278', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 9.74/10.00      inference('demod', [status(thm)], ['268', '277'])).
% 9.74/10.00  thf('279', plain,
% 9.74/10.00      (![X3 : $i, X4 : $i]:
% 9.74/10.00         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 9.74/10.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.74/10.00  thf('280', plain,
% 9.74/10.00      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 9.74/10.00      inference('sup-', [status(thm)], ['278', '279'])).
% 9.74/10.00  thf('281', plain, ((r1_tarski @ sk_A @ sk_B)),
% 9.74/10.00      inference('simplify', [status(thm)], ['280'])).
% 9.74/10.00  thf('282', plain, ($false), inference('demod', [status(thm)], ['0', '281'])).
% 9.74/10.00  
% 9.74/10.00  % SZS output end Refutation
% 9.74/10.00  
% 9.86/10.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
