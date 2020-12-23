%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sbL3mbOuPR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:08 EST 2020

% Result     : Theorem 6.44s
% Output     : Refutation 6.44s
% Verified   : 
% Statistics : Number of formulae       :  299 (7559 expanded)
%              Number of leaves         :   36 (2343 expanded)
%              Depth                    :   55
%              Number of atoms          : 2591 (84394 expanded)
%              Number of equality atoms :  145 (5125 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k10_relat_1 @ X35 @ X36 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('19',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ X22 ) @ ( k10_relat_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ k1_xboole_0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('33',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ X22 ) @ ( k10_relat_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','51'])).

thf('53',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('54',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('55',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','64','65','66','67'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('69',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k6_subset_1 @ X27 @ X28 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','81'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('84',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('86',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('88',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('95',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','93','94','95','96','97'])).

thf('99',plain,
    ( ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('105',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('106',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
      = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['103','118'])).

thf('120',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('121',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('126',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['131'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('133',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ ( k9_relat_1 @ X30 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('138',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['129','144'])).

thf('146',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('147',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('148',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('152',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['150','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('159',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('160',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
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
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','165'])).

thf('167',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('168',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('172',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('173',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('175',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('176',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k10_relat_1 @ X35 @ X36 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('178',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('182',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['175','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ X22 ) @ ( k10_relat_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['174','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['173','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['172','197'])).

thf('199',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('200',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['198','199','200','201','202'])).

thf('204',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['171','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('206',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('208',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207','208','209','210'])).

thf('212',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X33 ) @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('215',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('216',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['171','203'])).

thf('217',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['215','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['214','227'])).

thf('229',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['171','203'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k9_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['228','240','241','242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['213','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','253'])).

thf('255',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['259','260'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sbL3mbOuPR
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.44/6.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.44/6.70  % Solved by: fo/fo7.sh
% 6.44/6.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.44/6.70  % done 8971 iterations in 6.222s
% 6.44/6.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.44/6.70  % SZS output start Refutation
% 6.44/6.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.44/6.70  thf(sk_A_type, type, sk_A: $i).
% 6.44/6.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.44/6.70  thf(sk_B_type, type, sk_B: $i).
% 6.44/6.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.44/6.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.44/6.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.44/6.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.44/6.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.44/6.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.44/6.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.44/6.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.44/6.70  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 6.44/6.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.44/6.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.44/6.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.44/6.70  thf(t155_funct_1, axiom,
% 6.44/6.70    (![A:$i,B:$i]:
% 6.44/6.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.70       ( ( v2_funct_1 @ B ) =>
% 6.44/6.70         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 6.44/6.70  thf('0', plain,
% 6.44/6.70      (![X35 : $i, X36 : $i]:
% 6.44/6.70         (~ (v2_funct_1 @ X35)
% 6.44/6.70          | ((k10_relat_1 @ X35 @ X36)
% 6.44/6.70              = (k9_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 6.44/6.70          | ~ (v1_funct_1 @ X35)
% 6.44/6.70          | ~ (v1_relat_1 @ X35))),
% 6.44/6.70      inference('cnf', [status(esa)], [t155_funct_1])).
% 6.44/6.70  thf(t164_funct_1, conjecture,
% 6.44/6.70    (![A:$i,B:$i]:
% 6.44/6.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.70       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 6.44/6.70         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 6.44/6.70  thf(zf_stmt_0, negated_conjecture,
% 6.44/6.70    (~( ![A:$i,B:$i]:
% 6.44/6.70        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.70          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 6.44/6.70            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 6.44/6.70    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 6.44/6.70  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 6.44/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.70  thf(dt_k2_funct_1, axiom,
% 6.44/6.70    (![A:$i]:
% 6.44/6.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.44/6.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.44/6.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.44/6.70  thf('2', plain,
% 6.44/6.70      (![X25 : $i]:
% 6.44/6.70         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 6.44/6.70          | ~ (v1_funct_1 @ X25)
% 6.44/6.70          | ~ (v1_relat_1 @ X25))),
% 6.44/6.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.70  thf('3', plain,
% 6.44/6.70      (![X25 : $i]:
% 6.44/6.70         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.70          | ~ (v1_funct_1 @ X25)
% 6.44/6.70          | ~ (v1_relat_1 @ X25))),
% 6.44/6.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.70  thf(t154_funct_1, axiom,
% 6.44/6.70    (![A:$i,B:$i]:
% 6.44/6.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.70       ( ( v2_funct_1 @ B ) =>
% 6.44/6.70         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 6.44/6.70  thf('4', plain,
% 6.44/6.70      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.44/6.71  thf('5', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 6.44/6.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.44/6.71  thf(t147_funct_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.71       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 6.44/6.71         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 6.44/6.71  thf('6', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('7', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 6.44/6.71              = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['5', '6'])).
% 6.44/6.71  thf(t167_relat_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ B ) =>
% 6.44/6.71       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 6.44/6.71  thf('8', plain,
% 6.44/6.71      (![X18 : $i, X19 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 6.44/6.71          | ~ (v1_relat_1 @ X18))),
% 6.44/6.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.44/6.71  thf(t152_relat_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ B ) =>
% 6.44/6.71       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 6.44/6.71            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 6.44/6.71            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 6.44/6.71  thf('9', plain,
% 6.44/6.71      (![X16 : $i, X17 : $i]:
% 6.44/6.71         (((X16) = (k1_xboole_0))
% 6.44/6.71          | ~ (v1_relat_1 @ X17)
% 6.44/6.71          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 6.44/6.71          | ((k9_relat_1 @ X17 @ X16) != (k1_xboole_0)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t152_relat_1])).
% 6.44/6.71  thf('10', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)) != (k1_xboole_0))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['8', '9'])).
% 6.44/6.71  thf('11', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)) != (k1_xboole_0))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['10'])).
% 6.44/6.71  thf('12', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k1_xboole_0) != (k1_xboole_0))
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['7', '11'])).
% 6.44/6.71  thf('13', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['12'])).
% 6.44/6.71  thf('14', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 6.44/6.71              = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['5', '6'])).
% 6.44/6.71  thf('15', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['13', '14'])).
% 6.44/6.71  thf('16', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.44/6.71      inference('simplify', [status(thm)], ['15'])).
% 6.44/6.71  thf('17', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('18', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('19', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 6.44/6.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.44/6.71  thf(t178_relat_1, axiom,
% 6.44/6.71    (![A:$i,B:$i,C:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ C ) =>
% 6.44/6.71       ( ( r1_tarski @ A @ B ) =>
% 6.44/6.71         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 6.44/6.71  thf('20', plain,
% 6.44/6.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X22 @ X23)
% 6.44/6.71          | ~ (v1_relat_1 @ X24)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ X24 @ X22) @ (k10_relat_1 @ X24 @ X23)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t178_relat_1])).
% 6.44/6.71  thf('21', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ 
% 6.44/6.71           (k10_relat_1 @ X1 @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ X1))),
% 6.44/6.71      inference('sup-', [status(thm)], ['19', '20'])).
% 6.44/6.71  thf('22', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X1) @ k1_xboole_0) @ 
% 6.44/6.71           (k9_relat_1 @ X1 @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ X1)
% 6.44/6.71          | ~ (v1_funct_1 @ X1)
% 6.44/6.71          | ~ (v2_funct_1 @ X1)
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['18', '21'])).
% 6.44/6.71  thf('23', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ k1_xboole_0) @ 
% 6.44/6.71             (k9_relat_1 @ X0 @ X1)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['17', '22'])).
% 6.44/6.71  thf('24', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ k1_xboole_0) @ 
% 6.44/6.71           (k9_relat_1 @ X0 @ X1))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['23'])).
% 6.44/6.71  thf('25', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ k1_xboole_0) @ 
% 6.44/6.71           k1_xboole_0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['16', '24'])).
% 6.44/6.71  thf('26', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ k1_xboole_0) @ 
% 6.44/6.71             k1_xboole_0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['25'])).
% 6.44/6.71  thf(t3_xboole_1, axiom,
% 6.44/6.71    (![A:$i]:
% 6.44/6.71     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.44/6.71  thf('27', plain,
% 6.44/6.71      (![X10 : $i]:
% 6.44/6.71         (((X10) = (k1_xboole_0)) | ~ (r1_tarski @ X10 @ k1_xboole_0))),
% 6.44/6.71      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.44/6.71  thf('28', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['26', '27'])).
% 6.44/6.71  thf('29', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('30', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('31', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf(t146_relat_1, axiom,
% 6.44/6.71    (![A:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ A ) =>
% 6.44/6.71       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 6.44/6.71  thf('32', plain,
% 6.44/6.71      (![X15 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 6.44/6.71          | ~ (v1_relat_1 @ X15))),
% 6.44/6.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 6.44/6.71  thf('33', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('34', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('35', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('36', plain,
% 6.44/6.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X22 @ X23)
% 6.44/6.71          | ~ (v1_relat_1 @ X24)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ X24 @ X22) @ (k10_relat_1 @ X24 @ X23)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t178_relat_1])).
% 6.44/6.71  thf('37', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 6.44/6.71           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup-', [status(thm)], ['35', '36'])).
% 6.44/6.71  thf('38', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 6.44/6.71           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['34', '37'])).
% 6.44/6.71  thf('39', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 6.44/6.71             (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['33', '38'])).
% 6.44/6.71  thf('40', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 6.44/6.71           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['39'])).
% 6.44/6.71  thf('41', plain,
% 6.44/6.71      (((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 6.44/6.71         (k2_relat_1 @ sk_B))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['32', '40'])).
% 6.44/6.71  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('46', plain,
% 6.44/6.71      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 6.44/6.71        (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 6.44/6.71  thf('47', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('48', plain,
% 6.44/6.71      ((~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ((k9_relat_1 @ sk_B @ 
% 6.44/6.71            (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 6.44/6.71            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['46', '47'])).
% 6.44/6.71  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('51', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ 
% 6.44/6.71         (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 6.44/6.71         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 6.44/6.71      inference('demod', [status(thm)], ['48', '49', '50'])).
% 6.44/6.71  thf('52', plain,
% 6.44/6.71      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.44/6.71          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['31', '51'])).
% 6.44/6.71  thf('53', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('54', plain,
% 6.44/6.71      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 6.44/6.71        (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 6.44/6.71  thf('55', plain,
% 6.44/6.71      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['53', '54'])).
% 6.44/6.71  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('58', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('59', plain,
% 6.44/6.71      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 6.44/6.71  thf('60', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('61', plain,
% 6.44/6.71      ((~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ((k9_relat_1 @ sk_B @ 
% 6.44/6.71            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.44/6.71            = (k9_relat_1 @ sk_B @ sk_A)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['59', '60'])).
% 6.44/6.71  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('64', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.44/6.71         = (k9_relat_1 @ sk_B @ sk_A))),
% 6.44/6.71      inference('demod', [status(thm)], ['61', '62', '63'])).
% 6.44/6.71  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('68', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 6.44/6.71      inference('demod', [status(thm)], ['52', '64', '65', '66', '67'])).
% 6.44/6.71  thf(t138_funct_1, axiom,
% 6.44/6.71    (![A:$i,B:$i,C:$i]:
% 6.44/6.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 6.44/6.71       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 6.44/6.71         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 6.44/6.71  thf('69', plain,
% 6.44/6.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X26 @ (k6_subset_1 @ X27 @ X28))
% 6.44/6.71            = (k6_subset_1 @ (k10_relat_1 @ X26 @ X27) @ 
% 6.44/6.71               (k10_relat_1 @ X26 @ X28)))
% 6.44/6.71          | ~ (v1_funct_1 @ X26)
% 6.44/6.71          | ~ (v1_relat_1 @ X26))),
% 6.44/6.71      inference('cnf', [status(esa)], [t138_funct_1])).
% 6.44/6.71  thf(redefinition_k6_subset_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.44/6.71  thf('70', plain,
% 6.44/6.71      (![X11 : $i, X12 : $i]:
% 6.44/6.71         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 6.44/6.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.44/6.71  thf('71', plain,
% 6.44/6.71      (![X11 : $i, X12 : $i]:
% 6.44/6.71         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 6.44/6.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.44/6.71  thf('72', plain,
% 6.44/6.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 6.44/6.71            = (k4_xboole_0 @ (k10_relat_1 @ X26 @ X27) @ 
% 6.44/6.71               (k10_relat_1 @ X26 @ X28)))
% 6.44/6.71          | ~ (v1_funct_1 @ X26)
% 6.44/6.71          | ~ (v1_relat_1 @ X26))),
% 6.44/6.71      inference('demod', [status(thm)], ['69', '70', '71'])).
% 6.44/6.71  thf('73', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 6.44/6.71            = (k4_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71               (k9_relat_1 @ sk_B @ sk_A)))
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['68', '72'])).
% 6.44/6.71  thf('74', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ((k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 6.44/6.71              = (k4_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71                 (k9_relat_1 @ sk_B @ sk_A))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['30', '73'])).
% 6.44/6.71  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('77', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ((k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 6.44/6.71              = (k4_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71                 (k9_relat_1 @ sk_B @ sk_A))))),
% 6.44/6.71      inference('demod', [status(thm)], ['74', '75', '76'])).
% 6.44/6.71  thf('78', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ((k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 6.44/6.71              = (k4_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71                 (k9_relat_1 @ sk_B @ sk_A))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['29', '77'])).
% 6.44/6.71  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('81', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 6.44/6.71           = (k4_xboole_0 @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71              (k9_relat_1 @ sk_B @ sk_A)))),
% 6.44/6.71      inference('demod', [status(thm)], ['78', '79', '80'])).
% 6.44/6.71  thf('82', plain,
% 6.44/6.71      ((((k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 6.44/6.71          (k4_xboole_0 @ k1_xboole_0 @ sk_A))
% 6.44/6.71          = (k4_xboole_0 @ k1_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['28', '81'])).
% 6.44/6.71  thf(t17_xboole_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.44/6.71  thf('83', plain,
% 6.44/6.71      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 6.44/6.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.44/6.71  thf('84', plain,
% 6.44/6.71      (![X10 : $i]:
% 6.44/6.71         (((X10) = (k1_xboole_0)) | ~ (r1_tarski @ X10 @ k1_xboole_0))),
% 6.44/6.71      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.44/6.71  thf('85', plain,
% 6.44/6.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.44/6.71      inference('sup-', [status(thm)], ['83', '84'])).
% 6.44/6.71  thf(t100_xboole_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.44/6.71  thf('86', plain,
% 6.44/6.71      (![X3 : $i, X4 : $i]:
% 6.44/6.71         ((k4_xboole_0 @ X3 @ X4)
% 6.44/6.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.44/6.71  thf('87', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 6.44/6.71           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['85', '86'])).
% 6.44/6.71  thf(t2_boole, axiom,
% 6.44/6.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.44/6.71  thf('88', plain,
% 6.44/6.71      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 6.44/6.71      inference('cnf', [status(esa)], [t2_boole])).
% 6.44/6.71  thf('89', plain,
% 6.44/6.71      (![X3 : $i, X4 : $i]:
% 6.44/6.71         ((k4_xboole_0 @ X3 @ X4)
% 6.44/6.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.44/6.71  thf('90', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['88', '89'])).
% 6.44/6.71  thf(t3_boole, axiom,
% 6.44/6.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.44/6.71  thf('91', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 6.44/6.71      inference('cnf', [status(esa)], [t3_boole])).
% 6.44/6.71  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['90', '91'])).
% 6.44/6.71  thf('93', plain,
% 6.44/6.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['87', '92'])).
% 6.44/6.71  thf('94', plain,
% 6.44/6.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['87', '92'])).
% 6.44/6.71  thf('95', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('98', plain,
% 6.44/6.71      (((k10_relat_1 @ (k2_funct_1 @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['82', '93', '94', '95', '96', '97'])).
% 6.44/6.71  thf('99', plain,
% 6.44/6.71      ((((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['4', '98'])).
% 6.44/6.71  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('102', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('103', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 6.44/6.71  thf('104', plain,
% 6.44/6.71      (![X15 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 6.44/6.71          | ~ (v1_relat_1 @ X15))),
% 6.44/6.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 6.44/6.71  thf('105', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('106', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('107', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('108', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ 
% 6.44/6.71           (k10_relat_1 @ X1 @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ X1))),
% 6.44/6.71      inference('sup-', [status(thm)], ['19', '20'])).
% 6.44/6.71  thf('109', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ 
% 6.44/6.71           (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['107', '108'])).
% 6.44/6.71  thf('110', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ 
% 6.44/6.71             (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['106', '109'])).
% 6.44/6.71  thf('111', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ 
% 6.44/6.71           (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['110'])).
% 6.44/6.71  thf('112', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X1 @ k1_xboole_0) @ (k9_relat_1 @ X1 @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ X1)
% 6.44/6.71          | ~ (v1_funct_1 @ X1)
% 6.44/6.71          | ~ (v2_funct_1 @ X1)
% 6.44/6.71          | ~ (v1_relat_1 @ X1)
% 6.44/6.71          | ~ (v1_funct_1 @ X1)
% 6.44/6.71          | ~ (v2_funct_1 @ X1))),
% 6.44/6.71      inference('sup+', [status(thm)], ['105', '111'])).
% 6.44/6.71  thf('113', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X1)
% 6.44/6.71          | ~ (v1_funct_1 @ X1)
% 6.44/6.71          | ~ (v1_relat_1 @ X1)
% 6.44/6.71          | (r1_tarski @ (k9_relat_1 @ X1 @ k1_xboole_0) @ 
% 6.44/6.71             (k9_relat_1 @ X1 @ X0)))),
% 6.44/6.71      inference('simplify', [status(thm)], ['112'])).
% 6.44/6.71  thf('114', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ (k2_relat_1 @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['104', '113'])).
% 6.44/6.71  thf('115', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ (k2_relat_1 @ X0)))),
% 6.44/6.71      inference('simplify', [status(thm)], ['114'])).
% 6.44/6.71  thf('116', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('117', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ 
% 6.44/6.71              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))
% 6.44/6.71              = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['115', '116'])).
% 6.44/6.71  thf('118', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X0 @ 
% 6.44/6.71            (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))
% 6.44/6.71            = (k9_relat_1 @ X0 @ k1_xboole_0))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['117'])).
% 6.44/6.71  thf('119', plain,
% 6.44/6.71      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 6.44/6.71          = (k9_relat_1 @ sk_B @ k1_xboole_0))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['103', '118'])).
% 6.44/6.71  thf('120', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 6.44/6.71  thf('121', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('122', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('123', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('124', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 6.44/6.71         = (k1_xboole_0))),
% 6.44/6.71      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 6.44/6.71  thf('125', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)) != (k1_xboole_0))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['10'])).
% 6.44/6.71  thf('126', plain,
% 6.44/6.71      ((((k1_xboole_0) != (k1_xboole_0))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['124', '125'])).
% 6.44/6.71  thf('127', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('128', plain,
% 6.44/6.71      ((((k1_xboole_0) != (k1_xboole_0))
% 6.44/6.71        | ((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 6.44/6.71      inference('demod', [status(thm)], ['126', '127'])).
% 6.44/6.71  thf('129', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['128'])).
% 6.44/6.71  thf('130', plain,
% 6.44/6.71      (![X15 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 6.44/6.71          | ~ (v1_relat_1 @ X15))),
% 6.44/6.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 6.44/6.71  thf(d10_xboole_0, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.44/6.71  thf('131', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.44/6.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.44/6.71  thf('132', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.44/6.71      inference('simplify', [status(thm)], ['131'])).
% 6.44/6.71  thf(t146_funct_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ B ) =>
% 6.44/6.71       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 6.44/6.71         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 6.44/6.71  thf('133', plain,
% 6.44/6.71      (![X29 : $i, X30 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 6.44/6.71          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ (k9_relat_1 @ X30 @ X29)))
% 6.44/6.71          | ~ (v1_relat_1 @ X30))),
% 6.44/6.71      inference('cnf', [status(esa)], [t146_funct_1])).
% 6.44/6.71  thf('134', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 6.44/6.71             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['132', '133'])).
% 6.44/6.71  thf('135', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 6.44/6.71           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['130', '134'])).
% 6.44/6.71  thf('136', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 6.44/6.71             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 6.44/6.71      inference('simplify', [status(thm)], ['135'])).
% 6.44/6.71  thf('137', plain,
% 6.44/6.71      (![X18 : $i, X19 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 6.44/6.71          | ~ (v1_relat_1 @ X18))),
% 6.44/6.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.44/6.71  thf('138', plain,
% 6.44/6.71      (![X0 : $i, X2 : $i]:
% 6.44/6.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.44/6.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.44/6.71  thf('139', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 6.44/6.71          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['137', '138'])).
% 6.44/6.71  thf('140', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup-', [status(thm)], ['136', '139'])).
% 6.44/6.71  thf('141', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['140'])).
% 6.44/6.71  thf('142', plain,
% 6.44/6.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 6.44/6.71            = (k4_xboole_0 @ (k10_relat_1 @ X26 @ X27) @ 
% 6.44/6.71               (k10_relat_1 @ X26 @ X28)))
% 6.44/6.71          | ~ (v1_funct_1 @ X26)
% 6.44/6.71          | ~ (v1_relat_1 @ X26))),
% 6.44/6.71      inference('demod', [status(thm)], ['69', '70', '71'])).
% 6.44/6.71  thf('143', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ X1))
% 6.44/6.71            = (k4_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['141', '142'])).
% 6.44/6.71  thf('144', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k10_relat_1 @ X0 @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ X1))
% 6.44/6.71              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 6.44/6.71      inference('simplify', [status(thm)], ['143'])).
% 6.44/6.71  thf('145', plain,
% 6.44/6.71      ((((k10_relat_1 @ sk_B @ 
% 6.44/6.71          (k4_xboole_0 @ (k2_relat_1 @ sk_B) @ k1_xboole_0))
% 6.44/6.71          = (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['129', '144'])).
% 6.44/6.71  thf('146', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 6.44/6.71      inference('cnf', [status(esa)], [t3_boole])).
% 6.44/6.71  thf('147', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 6.44/6.71      inference('cnf', [status(esa)], [t3_boole])).
% 6.44/6.71  thf('148', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('149', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('150', plain,
% 6.44/6.71      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 6.44/6.71  thf('151', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.44/6.71      inference('simplify', [status(thm)], ['131'])).
% 6.44/6.71  thf('152', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('153', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71              = (k2_relat_1 @ X0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['151', '152'])).
% 6.44/6.71  thf('154', plain,
% 6.44/6.71      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['150', '153'])).
% 6.44/6.71  thf('155', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('156', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('157', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['154', '155', '156'])).
% 6.44/6.71  thf('158', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('159', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('160', plain,
% 6.44/6.71      (![X18 : $i, X19 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 6.44/6.71          | ~ (v1_relat_1 @ X18))),
% 6.44/6.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.44/6.71  thf('161', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 6.44/6.71           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 6.44/6.71          | ~ (v1_relat_1 @ X1)
% 6.44/6.71          | ~ (v1_funct_1 @ X1)
% 6.44/6.71          | ~ (v2_funct_1 @ X1)
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['159', '160'])).
% 6.44/6.71  thf('162', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 6.44/6.71             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['158', '161'])).
% 6.44/6.71  thf('163', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 6.44/6.71           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['162'])).
% 6.44/6.71  thf('164', plain,
% 6.44/6.71      (![X0 : $i, X2 : $i]:
% 6.44/6.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.44/6.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.44/6.71  thf('165', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.44/6.71               (k9_relat_1 @ X0 @ X1))
% 6.44/6.71          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['163', '164'])).
% 6.44/6.71  thf('166', plain,
% 6.44/6.71      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 6.44/6.71        | ((k1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71            = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B))),
% 6.44/6.71      inference('sup-', [status(thm)], ['157', '165'])).
% 6.44/6.71  thf('167', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['154', '155', '156'])).
% 6.44/6.71  thf('168', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('169', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('170', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('171', plain,
% 6.44/6.71      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 6.44/6.71        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 6.44/6.71      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 6.44/6.71  thf('172', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('173', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('174', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['140'])).
% 6.44/6.71  thf('175', plain,
% 6.44/6.71      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 6.44/6.71  thf('176', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('177', plain,
% 6.44/6.71      (![X35 : $i, X36 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X35)
% 6.44/6.71          | ((k10_relat_1 @ X35 @ X36)
% 6.44/6.71              = (k9_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 6.44/6.71          | ~ (v1_funct_1 @ X35)
% 6.44/6.71          | ~ (v1_relat_1 @ X35))),
% 6.44/6.71      inference('cnf', [status(esa)], [t155_funct_1])).
% 6.44/6.71  thf('178', plain,
% 6.44/6.71      (![X15 : $i]:
% 6.44/6.71         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 6.44/6.71          | ~ (v1_relat_1 @ X15))),
% 6.44/6.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 6.44/6.71  thf('179', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['177', '178'])).
% 6.44/6.71  thf('180', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['176', '179'])).
% 6.44/6.71  thf('181', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['180'])).
% 6.44/6.71  thf(t170_relat_1, axiom,
% 6.44/6.71    (![A:$i,B:$i]:
% 6.44/6.71     ( ( v1_relat_1 @ B ) =>
% 6.44/6.71       ( r1_tarski @
% 6.44/6.71         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 6.44/6.71  thf('182', plain,
% 6.44/6.71      (![X20 : $i, X21 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ 
% 6.44/6.71           (k10_relat_1 @ X20 @ (k2_relat_1 @ X20)))
% 6.44/6.71          | ~ (v1_relat_1 @ X20))),
% 6.44/6.71      inference('cnf', [status(esa)], [t170_relat_1])).
% 6.44/6.71  thf('183', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.44/6.71           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup+', [status(thm)], ['181', '182'])).
% 6.44/6.71  thf('184', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0)
% 6.44/6.71          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.44/6.71             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 6.44/6.71      inference('simplify', [status(thm)], ['183'])).
% 6.44/6.71  thf('185', plain,
% 6.44/6.71      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ (k1_relat_1 @ sk_B))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['175', '184'])).
% 6.44/6.71  thf('186', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('187', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('188', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('189', plain,
% 6.44/6.71      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ (k1_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 6.44/6.71  thf('190', plain,
% 6.44/6.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X22 @ X23)
% 6.44/6.71          | ~ (v1_relat_1 @ X24)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ X24 @ X22) @ (k10_relat_1 @ X24 @ X23)))),
% 6.44/6.71      inference('cnf', [status(esa)], [t178_relat_1])).
% 6.44/6.71  thf('191', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ 
% 6.44/6.71           (k10_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))) @ 
% 6.44/6.71           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('sup-', [status(thm)], ['189', '190'])).
% 6.44/6.71  thf('192', plain,
% 6.44/6.71      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 6.44/6.71         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k1_relat_1 @ sk_B)))
% 6.44/6.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['174', '191'])).
% 6.44/6.71  thf('193', plain,
% 6.44/6.71      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 6.44/6.71           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k1_relat_1 @ sk_B))))),
% 6.44/6.71      inference('simplify', [status(thm)], ['192'])).
% 6.44/6.71  thf('194', plain,
% 6.44/6.71      ((~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 6.44/6.71           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k1_relat_1 @ sk_B))))),
% 6.44/6.71      inference('sup-', [status(thm)], ['173', '193'])).
% 6.44/6.71  thf('195', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('196', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('197', plain,
% 6.44/6.71      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 6.44/6.71        (k10_relat_1 @ (k2_funct_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 6.44/6.71      inference('demod', [status(thm)], ['194', '195', '196'])).
% 6.44/6.71  thf('198', plain,
% 6.44/6.71      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 6.44/6.71         (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['172', '197'])).
% 6.44/6.71  thf('199', plain,
% 6.44/6.71      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['154', '155', '156'])).
% 6.44/6.71  thf('200', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('201', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('202', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('203', plain,
% 6.44/6.71      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['198', '199', '200', '201', '202'])).
% 6.44/6.71  thf('204', plain,
% 6.44/6.71      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['171', '203'])).
% 6.44/6.71  thf('205', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['180'])).
% 6.44/6.71  thf('206', plain,
% 6.44/6.71      ((((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 6.44/6.71          = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['204', '205'])).
% 6.44/6.71  thf('207', plain,
% 6.44/6.71      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 6.44/6.71  thf('208', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('209', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('210', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('211', plain,
% 6.44/6.71      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.44/6.71      inference('demod', [status(thm)], ['206', '207', '208', '209', '210'])).
% 6.44/6.71  thf('212', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('213', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 6.44/6.71              (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)) = (X0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['211', '212'])).
% 6.44/6.71  thf('214', plain,
% 6.44/6.71      (![X33 : $i, X34 : $i]:
% 6.44/6.71         (~ (v2_funct_1 @ X33)
% 6.44/6.71          | ((k9_relat_1 @ X33 @ X34)
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ X33) @ X34))
% 6.44/6.71          | ~ (v1_funct_1 @ X33)
% 6.44/6.71          | ~ (v1_relat_1 @ X33))),
% 6.44/6.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.44/6.71  thf('215', plain,
% 6.44/6.71      (![X25 : $i]:
% 6.44/6.71         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 6.44/6.71          | ~ (v1_funct_1 @ X25)
% 6.44/6.71          | ~ (v1_relat_1 @ X25))),
% 6.44/6.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.44/6.71  thf('216', plain,
% 6.44/6.71      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['171', '203'])).
% 6.44/6.71  thf('217', plain,
% 6.44/6.71      (![X18 : $i, X19 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 6.44/6.71          | ~ (v1_relat_1 @ X18))),
% 6.44/6.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.44/6.71  thf('218', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71           (k2_relat_1 @ sk_B))
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.44/6.71      inference('sup+', [status(thm)], ['216', '217'])).
% 6.44/6.71  thf('219', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71             (k2_relat_1 @ sk_B)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['215', '218'])).
% 6.44/6.71  thf('220', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('221', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('222', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 6.44/6.71          (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['219', '220', '221'])).
% 6.44/6.71  thf('223', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('224', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ((k9_relat_1 @ sk_B @ 
% 6.44/6.71              (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 6.44/6.71              = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['222', '223'])).
% 6.44/6.71  thf('225', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('226', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('227', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k9_relat_1 @ sk_B @ 
% 6.44/6.71           (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 6.44/6.71           = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 6.44/6.71      inference('demod', [status(thm)], ['224', '225', '226'])).
% 6.44/6.71  thf('228', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 6.44/6.71            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 6.44/6.71          | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['214', '227'])).
% 6.44/6.71  thf('229', plain,
% 6.44/6.71      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['171', '203'])).
% 6.44/6.71  thf('230', plain,
% 6.44/6.71      (![X0 : $i, X1 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 6.44/6.71           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 6.44/6.71          | ~ (v2_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_funct_1 @ X0)
% 6.44/6.71          | ~ (v1_relat_1 @ X0))),
% 6.44/6.71      inference('simplify', [status(thm)], ['162'])).
% 6.44/6.71  thf('231', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))
% 6.44/6.71          | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['229', '230'])).
% 6.44/6.71  thf('232', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('233', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('234', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('235', plain,
% 6.44/6.71      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))),
% 6.44/6.71      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 6.44/6.71  thf('236', plain,
% 6.44/6.71      (![X31 : $i, X32 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 6.44/6.71          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 6.44/6.71          | ~ (v1_funct_1 @ X32)
% 6.44/6.71          | ~ (v1_relat_1 @ X32))),
% 6.44/6.71      inference('cnf', [status(esa)], [t147_funct_1])).
% 6.44/6.71  thf('237', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ((k9_relat_1 @ sk_B @ 
% 6.44/6.71              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 6.44/6.71              = (k9_relat_1 @ sk_B @ X0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['235', '236'])).
% 6.44/6.71  thf('238', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('239', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('240', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 6.44/6.71           = (k9_relat_1 @ sk_B @ X0))),
% 6.44/6.71      inference('demod', [status(thm)], ['237', '238', '239'])).
% 6.44/6.71  thf('241', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('242', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('243', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('244', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         ((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 6.44/6.71      inference('demod', [status(thm)], ['228', '240', '241', '242', '243'])).
% 6.44/6.71  thf('245', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 6.44/6.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 6.44/6.71              = (X0)))),
% 6.44/6.71      inference('demod', [status(thm)], ['213', '244'])).
% 6.44/6.71  thf('246', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 6.44/6.71              = (X0))
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['3', '245'])).
% 6.44/6.71  thf('247', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('248', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('249', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 6.44/6.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.44/6.71          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 6.44/6.71      inference('demod', [status(thm)], ['246', '247', '248'])).
% 6.44/6.71  thf('250', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (v1_relat_1 @ sk_B)
% 6.44/6.71          | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 6.44/6.71          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 6.44/6.71              = (X0)))),
% 6.44/6.71      inference('sup-', [status(thm)], ['2', '249'])).
% 6.44/6.71  thf('251', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('252', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('253', plain,
% 6.44/6.71      (![X0 : $i]:
% 6.44/6.71         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 6.44/6.71          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 6.44/6.71              = (X0)))),
% 6.44/6.71      inference('demod', [status(thm)], ['250', '251', '252'])).
% 6.44/6.71  thf('254', plain,
% 6.44/6.71      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 6.44/6.71         = (sk_A))),
% 6.44/6.71      inference('sup-', [status(thm)], ['1', '253'])).
% 6.44/6.71  thf('255', plain,
% 6.44/6.71      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 6.44/6.71        | ~ (v1_relat_1 @ sk_B)
% 6.44/6.71        | ~ (v1_funct_1 @ sk_B)
% 6.44/6.71        | ~ (v2_funct_1 @ sk_B))),
% 6.44/6.71      inference('sup+', [status(thm)], ['0', '254'])).
% 6.44/6.71  thf('256', plain, ((v1_relat_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('257', plain, ((v1_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('258', plain, ((v2_funct_1 @ sk_B)),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('259', plain,
% 6.44/6.71      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 6.44/6.71      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 6.44/6.71  thf('260', plain,
% 6.44/6.71      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 6.44/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.71  thf('261', plain, ($false),
% 6.44/6.71      inference('simplify_reflect-', [status(thm)], ['259', '260'])).
% 6.44/6.71  
% 6.44/6.71  % SZS output end Refutation
% 6.44/6.71  
% 6.44/6.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
