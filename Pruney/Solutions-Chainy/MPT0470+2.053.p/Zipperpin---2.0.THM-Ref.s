%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OgJo7PjmtP

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:34 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 166 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  787 (1069 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','31'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('46',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('55',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('56',plain,
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

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('75',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('87',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['52','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['89','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OgJo7PjmtP
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 1575 iterations in 0.730s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.18  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.00/1.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.00/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i > $i).
% 1.00/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.18  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.00/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(cc1_relat_1, axiom,
% 1.00/1.18    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.00/1.18  thf('0', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.00/1.18  thf(dt_k5_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.00/1.18       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X17 : $i, X18 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X17)
% 1.00/1.18          | ~ (v1_relat_1 @ X18)
% 1.00/1.18          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.00/1.18  thf('2', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.00/1.18  thf(t60_relat_1, axiom,
% 1.00/1.18    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.00/1.18     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.00/1.18  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.00/1.18  thf(t45_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( r1_tarski @
% 1.00/1.18             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X21 : $i, X22 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X21)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 1.00/1.18             (k2_relat_1 @ X21))
% 1.00/1.18          | ~ (v1_relat_1 @ X22))),
% 1.00/1.18      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.00/1.18  thf('5', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18           k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['3', '4'])).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18             k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['2', '5'])).
% 1.00/1.18  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.00/1.18  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18             k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['6', '7'])).
% 1.00/1.18  thf(t28_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('10', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['8', '9'])).
% 1.00/1.18  thf(t3_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.00/1.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.18            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.00/1.18  thf('11', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.00/1.18  thf('12', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 1.00/1.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf(t4_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.18            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.00/1.18          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['14', '15'])).
% 1.00/1.18  thf('17', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X8 @ X9)
% 1.00/1.18          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.00/1.18          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf(d1_xboole_0, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.00/1.18  thf('20', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['19', '20'])).
% 1.00/1.18  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.00/1.18      inference('demod', [status(thm)], ['21', '22'])).
% 1.00/1.18  thf('24', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.00/1.18      inference('demod', [status(thm)], ['16', '23'])).
% 1.00/1.18  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.00/1.18      inference('sup-', [status(thm)], ['11', '24'])).
% 1.00/1.18  thf('26', plain,
% 1.00/1.18      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.00/1.18  thf('27', plain,
% 1.00/1.18      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.00/1.18          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['25', '28'])).
% 1.00/1.18  thf(l13_xboole_0, axiom,
% 1.00/1.18    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['29', '30'])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '31'])).
% 1.00/1.18  thf(fc9_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.00/1.18       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (![X20 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ (k2_relat_1 @ X20))
% 1.00/1.18          | ~ (v1_relat_1 @ X20)
% 1.00/1.18          | (v1_xboole_0 @ X20))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['32', '33'])).
% 1.00/1.18  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['34', '35'])).
% 1.00/1.18  thf('37', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['1', '36'])).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['37'])).
% 1.00/1.18  thf('39', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['0', '38'])).
% 1.00/1.18  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('41', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['39', '40'])).
% 1.00/1.18  thf('42', plain,
% 1.00/1.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.00/1.18  thf('43', plain,
% 1.00/1.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.00/1.18  thf('44', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['42', '43'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.00/1.18  thf(t62_relat_1, conjecture,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.00/1.18         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i]:
% 1.00/1.18        ( ( v1_relat_1 @ A ) =>
% 1.00/1.18          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.00/1.18            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.00/1.18        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.00/1.18      inference('split', [status(esa)], ['46'])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      ((![X0 : $i]:
% 1.00/1.18          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['45', '47'])).
% 1.00/1.18  thf('49', plain,
% 1.00/1.18      ((![X0 : $i, X1 : $i]:
% 1.00/1.18          (((X0) != (k1_xboole_0))
% 1.00/1.18           | ~ (v1_xboole_0 @ X0)
% 1.00/1.18           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 1.00/1.18           | ~ (v1_xboole_0 @ X1)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['44', '48'])).
% 1.00/1.18  thf('50', plain,
% 1.00/1.18      ((![X1 : $i]:
% 1.00/1.18          (~ (v1_xboole_0 @ X1)
% 1.00/1.18           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 1.00/1.18           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.00/1.18      inference('simplify', [status(thm)], ['49'])).
% 1.00/1.18  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      ((![X1 : $i]:
% 1.00/1.18          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 1.00/1.18         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.00/1.18      inference('simplify_reflect+', [status(thm)], ['50', '51'])).
% 1.00/1.18  thf('53', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.00/1.18  thf('54', plain,
% 1.00/1.18      (![X17 : $i, X18 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X17)
% 1.00/1.18          | ~ (v1_relat_1 @ X18)
% 1.00/1.18          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.00/1.18  thf('55', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.00/1.18  thf('56', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.00/1.18  thf(t46_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.00/1.18             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.00/1.18  thf('57', plain,
% 1.00/1.18      (![X23 : $i, X24 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X23)
% 1.00/1.18          | ((k1_relat_1 @ (k5_relat_1 @ X24 @ X23)) = (k1_relat_1 @ X24))
% 1.00/1.18          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 1.00/1.18          | ~ (v1_relat_1 @ X24))),
% 1.00/1.18      inference('cnf', [status(esa)], [t46_relat_1])).
% 1.00/1.18  thf('58', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.00/1.18          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.00/1.18              = (k1_relat_1 @ k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['56', '57'])).
% 1.00/1.18  thf('59', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 1.00/1.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.00/1.18  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.00/1.18  thf('61', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ k1_xboole_0)
% 1.00/1.18          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['55', '61'])).
% 1.00/1.18  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('64', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['62', '63'])).
% 1.00/1.18  thf(fc8_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.00/1.18       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.00/1.18  thf('65', plain,
% 1.00/1.18      (![X19 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ (k1_relat_1 @ X19))
% 1.00/1.18          | ~ (v1_relat_1 @ X19)
% 1.00/1.18          | (v1_xboole_0 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.00/1.18  thf('66', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['64', '65'])).
% 1.00/1.18  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('68', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['66', '67'])).
% 1.00/1.18  thf('69', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['54', '68'])).
% 1.00/1.18  thf('70', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['69'])).
% 1.00/1.18  thf('71', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['53', '70'])).
% 1.00/1.18  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('73', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['71', '72'])).
% 1.00/1.18  thf('74', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['42', '43'])).
% 1.00/1.18  thf('75', plain,
% 1.00/1.18      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.00/1.18  thf('76', plain,
% 1.00/1.18      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('split', [status(esa)], ['46'])).
% 1.00/1.18  thf('77', plain,
% 1.00/1.18      ((![X0 : $i]:
% 1.00/1.18          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['75', '76'])).
% 1.00/1.18  thf('78', plain,
% 1.00/1.18      ((![X0 : $i, X1 : $i]:
% 1.00/1.18          (((X0) != (k1_xboole_0))
% 1.00/1.18           | ~ (v1_xboole_0 @ X0)
% 1.00/1.18           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.00/1.18           | ~ (v1_xboole_0 @ X1)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['74', '77'])).
% 1.00/1.18  thf('79', plain,
% 1.00/1.18      ((![X1 : $i]:
% 1.00/1.18          (~ (v1_xboole_0 @ X1)
% 1.00/1.18           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.00/1.18           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('simplify', [status(thm)], ['78'])).
% 1.00/1.18  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('81', plain,
% 1.00/1.18      ((![X1 : $i]:
% 1.00/1.18          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('simplify_reflect+', [status(thm)], ['79', '80'])).
% 1.00/1.18  thf('82', plain,
% 1.00/1.18      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.00/1.18         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['73', '81'])).
% 1.00/1.18  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('85', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.00/1.18  thf('86', plain,
% 1.00/1.18      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.00/1.18       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.00/1.18      inference('split', [status(esa)], ['46'])).
% 1.00/1.18  thf('87', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.00/1.18      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 1.00/1.18  thf('88', plain,
% 1.00/1.18      (![X1 : $i]:
% 1.00/1.18         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1)))),
% 1.00/1.18      inference('simpl_trail', [status(thm)], ['52', '87'])).
% 1.00/1.18  thf('89', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['41', '88'])).
% 1.00/1.18  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.18  thf('92', plain, ($false),
% 1.00/1.18      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
