%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VZbpy4VgKU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 473 expanded)
%              Number of leaves         :   29 ( 161 expanded)
%              Depth                    :   32
%              Number of atoms          :  814 (3136 expanded)
%              Number of equality atoms :   82 ( 302 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k6_subset_1 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k6_subset_1 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X22 @ X21 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X22 ) @ ( k4_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('23',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','47'])).

thf('49',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','50'])).

thf('52',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','51'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X25 ) @ ( k4_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','43'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('64',plain,(
    ! [X20: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','51'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','67'])).

thf('69',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','50'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['73'])).

thf('89',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['75','89'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    $false ),
    inference(simplify,[status(thm)],['94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VZbpy4VgKU
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:10:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.07  % Solved by: fo/fo7.sh
% 0.89/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.07  % done 1544 iterations in 0.622s
% 0.89/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.07  % SZS output start Refutation
% 0.89/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.07  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.89/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.07  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.89/1.07  thf(dt_k5_relat_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.89/1.07       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.89/1.07  thf('0', plain,
% 0.89/1.07      (![X17 : $i, X18 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X18)
% 0.89/1.07          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.07  thf(t3_boole, axiom,
% 0.89/1.07    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.07  thf('1', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.07  thf(redefinition_k6_subset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.07  thf('2', plain,
% 0.89/1.07      (![X11 : $i, X12 : $i]:
% 0.89/1.07         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.07  thf('3', plain, (![X3 : $i]: ((k6_subset_1 @ X3 @ k1_xboole_0) = (X3))),
% 0.89/1.07      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.07  thf('4', plain, (![X3 : $i]: ((k6_subset_1 @ X3 @ k1_xboole_0) = (X3))),
% 0.89/1.07      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.07  thf(t48_xboole_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.07  thf('5', plain,
% 0.89/1.07      (![X4 : $i, X5 : $i]:
% 0.89/1.07         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.89/1.07           = (k3_xboole_0 @ X4 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.07  thf('6', plain,
% 0.89/1.07      (![X11 : $i, X12 : $i]:
% 0.89/1.07         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.07  thf('7', plain,
% 0.89/1.07      (![X11 : $i, X12 : $i]:
% 0.89/1.07         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.07  thf('8', plain,
% 0.89/1.07      (![X4 : $i, X5 : $i]:
% 0.89/1.07         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.89/1.07           = (k3_xboole_0 @ X4 @ X5))),
% 0.89/1.07      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.89/1.07  thf('9', plain,
% 0.89/1.07      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['4', '8'])).
% 0.89/1.07  thf(t2_boole, axiom,
% 0.89/1.07    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.89/1.07  thf('10', plain,
% 0.89/1.07      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.07      inference('cnf', [status(esa)], [t2_boole])).
% 0.89/1.07  thf('11', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf(t41_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( v1_relat_1 @ B ) =>
% 0.89/1.07           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.89/1.07             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.89/1.07  thf('12', plain,
% 0.89/1.07      (![X21 : $i, X22 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X21)
% 0.89/1.07          | ((k4_relat_1 @ (k6_subset_1 @ X22 @ X21))
% 0.89/1.07              = (k6_subset_1 @ (k4_relat_1 @ X22) @ (k4_relat_1 @ X21)))
% 0.89/1.07          | ~ (v1_relat_1 @ X22))),
% 0.89/1.07      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.89/1.07  thf('13', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['11', '12'])).
% 0.89/1.07  thf('14', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k4_relat_1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['13'])).
% 0.89/1.07  thf('15', plain,
% 0.89/1.07      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.89/1.07        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['3', '14'])).
% 0.89/1.07  thf('16', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.07  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('18', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['16', '17'])).
% 0.89/1.07  thf(t62_relat_1, conjecture,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.89/1.07         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.07    (~( ![A:$i]:
% 0.89/1.07        ( ( v1_relat_1 @ A ) =>
% 0.89/1.07          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.89/1.07            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.89/1.07    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.89/1.07  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(l13_xboole_0, axiom,
% 0.89/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.07  thf('20', plain,
% 0.89/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.07  thf(cc1_relat_1, axiom,
% 0.89/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.89/1.07  thf('21', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.89/1.07  thf('22', plain,
% 0.89/1.07      (![X17 : $i, X18 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X18)
% 0.89/1.07          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.07  thf('23', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.89/1.07  thf(t60_relat_1, axiom,
% 0.89/1.07    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.89/1.07     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.89/1.07  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.89/1.07  thf(t46_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( v1_relat_1 @ B ) =>
% 0.89/1.07           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.89/1.07             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.07  thf('25', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X23)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X24 @ X23)) = (k1_relat_1 @ X24))
% 0.89/1.07          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 0.89/1.07          | ~ (v1_relat_1 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.89/1.07  thf('26', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.89/1.07              = (k1_relat_1 @ k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.89/1.07  thf('27', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.89/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.89/1.07  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.89/1.07  thf('29', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.89/1.07  thf('30', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['23', '29'])).
% 0.89/1.07  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('32', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['30', '31'])).
% 0.89/1.07  thf(fc8_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.89/1.07       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.89/1.07  thf('33', plain,
% 0.89/1.07      (![X19 : $i]:
% 0.89/1.07         (~ (v1_xboole_0 @ (k1_relat_1 @ X19))
% 0.89/1.07          | ~ (v1_relat_1 @ X19)
% 0.89/1.07          | (v1_xboole_0 @ X19))),
% 0.89/1.07      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.89/1.07  thf('34', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.89/1.07  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('36', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.07  thf('37', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['22', '36'])).
% 0.89/1.07  thf('38', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['37'])).
% 0.89/1.07  thf('39', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['21', '38'])).
% 0.89/1.07  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('41', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.07  thf('42', plain,
% 0.89/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.07  thf('43', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['41', '42'])).
% 0.89/1.07  thf('44', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_xboole_0 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X1))),
% 0.89/1.07      inference('sup+', [status(thm)], ['20', '43'])).
% 0.89/1.07  thf('45', plain,
% 0.89/1.07      (![X17 : $i, X18 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X18)
% 0.89/1.07          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.07  thf('46', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         ((v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_xboole_0 @ X1)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X1))),
% 0.89/1.07      inference('sup+', [status(thm)], ['44', '45'])).
% 0.89/1.07  thf('47', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X1)
% 0.89/1.07          | ~ (v1_xboole_0 @ X1)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v1_relat_1 @ k1_xboole_0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['46'])).
% 0.89/1.07  thf('48', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_xboole_0 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['19', '47'])).
% 0.89/1.07  thf('49', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.89/1.07  thf('50', plain,
% 0.89/1.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.89/1.07      inference('clc', [status(thm)], ['48', '49'])).
% 0.89/1.07  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.07      inference('sup-', [status(thm)], ['18', '50'])).
% 0.89/1.07  thf('52', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.07      inference('demod', [status(thm)], ['15', '51'])).
% 0.89/1.07  thf(t54_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( v1_relat_1 @ B ) =>
% 0.89/1.07           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.89/1.07             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.07  thf('53', plain,
% 0.89/1.07      (![X25 : $i, X26 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X25)
% 0.89/1.07          | ((k4_relat_1 @ (k5_relat_1 @ X26 @ X25))
% 0.89/1.07              = (k5_relat_1 @ (k4_relat_1 @ X25) @ (k4_relat_1 @ X26)))
% 0.89/1.07          | ~ (v1_relat_1 @ X26))),
% 0.89/1.07      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.89/1.07  thf('54', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.89/1.07            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.07  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.07      inference('sup-', [status(thm)], ['18', '50'])).
% 0.89/1.07  thf('56', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.89/1.07            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.07  thf(dt_k4_relat_1, axiom,
% 0.89/1.07    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.89/1.07  thf('57', plain,
% 0.89/1.07      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('58', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_xboole_0 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X1))),
% 0.89/1.07      inference('sup+', [status(thm)], ['20', '43'])).
% 0.89/1.07  thf('59', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_xboole_0 @ X1)
% 0.89/1.07          | ((k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['57', '58'])).
% 0.89/1.07  thf('60', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup+', [status(thm)], ['56', '59'])).
% 0.89/1.07  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('62', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['60', '61'])).
% 0.89/1.07  thf('63', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['62'])).
% 0.89/1.07  thf(involutiveness_k4_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.07  thf('64', plain,
% 0.89/1.07      (![X20 : $i]:
% 0.89/1.07         (((k4_relat_1 @ (k4_relat_1 @ X20)) = (X20)) | ~ (v1_relat_1 @ X20))),
% 0.89/1.07      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.89/1.07  thf('65', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['63', '64'])).
% 0.89/1.07  thf('66', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.07      inference('demod', [status(thm)], ['15', '51'])).
% 0.89/1.07  thf('67', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['65', '66'])).
% 0.89/1.07  thf('68', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['0', '67'])).
% 0.89/1.07  thf('69', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.07      inference('sup-', [status(thm)], ['18', '50'])).
% 0.89/1.07  thf('70', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.07  thf('71', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['70'])).
% 0.89/1.07  thf('72', plain,
% 0.89/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.07  thf('73', plain,
% 0.89/1.07      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.89/1.07        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('74', plain,
% 0.89/1.07      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.89/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.89/1.07      inference('split', [status(esa)], ['73'])).
% 0.89/1.07  thf('75', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.89/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['72', '74'])).
% 0.89/1.07  thf('76', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.07  thf('77', plain,
% 0.89/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.07  thf('78', plain,
% 0.89/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.07  thf('79', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]:
% 0.89/1.07         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.07      inference('sup+', [status(thm)], ['77', '78'])).
% 0.89/1.07  thf('80', plain,
% 0.89/1.07      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.89/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.07      inference('split', [status(esa)], ['73'])).
% 0.89/1.07  thf('81', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          (((X0) != (k1_xboole_0))
% 0.89/1.07           | ~ (v1_xboole_0 @ X0)
% 0.89/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 0.89/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['79', '80'])).
% 0.89/1.07  thf('82', plain,
% 0.89/1.07      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.89/1.07         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.89/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['81'])).
% 0.89/1.07  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('84', plain,
% 0.89/1.07      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.89/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.07      inference('simplify_reflect+', [status(thm)], ['82', '83'])).
% 0.89/1.07  thf('85', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_A))
% 0.89/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['76', '84'])).
% 0.89/1.07  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('87', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['85', '86'])).
% 0.89/1.07  thf('88', plain,
% 0.89/1.07      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.89/1.07       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.89/1.07      inference('split', [status(esa)], ['73'])).
% 0.89/1.07  thf('89', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.89/1.07      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.89/1.07  thf('90', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.07      inference('simpl_trail', [status(thm)], ['75', '89'])).
% 0.89/1.07  thf('91', plain,
% 0.89/1.07      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_A)
% 0.89/1.07        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['71', '90'])).
% 0.89/1.07  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.07  thf('94', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.89/1.07      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.89/1.07  thf('95', plain, ($false), inference('simplify', [status(thm)], ['94'])).
% 0.89/1.07  
% 0.89/1.07  % SZS output end Refutation
% 0.89/1.07  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
