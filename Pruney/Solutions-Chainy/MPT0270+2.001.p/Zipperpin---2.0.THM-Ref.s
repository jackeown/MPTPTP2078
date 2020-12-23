%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aIMwqi1zqP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:11 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  172 (1590 expanded)
%              Number of leaves         :   29 ( 449 expanded)
%              Depth                    :   33
%              Number of atoms          : 1603 (16362 expanded)
%              Number of equality atoms :  132 (1426 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) )
        = X46 )
      | ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['14'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( X17
       != ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) )
        = X46 )
      | ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('29',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X22: $i] :
      ( ( X20 = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_A ) )
        | ( X0
          = ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X45 ) )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('48',plain,
    ( ( ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
       != sk_B )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('50',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
     != sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) )
       != sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
         != sk_B )
        | ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','51'])).

thf('53',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) )
        = X46 )
      | ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ X0 @ sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ X0 @ sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('57',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','58'])).

thf('60',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X10 @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_D @ X13 @ X10 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','17'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ X18 @ X15 )
      | ( X17
       != ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['61','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('78',plain,(
    ! [X20: $i,X22: $i] :
      ( ( X20 = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X2
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('85',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X47 ) )
        = X46 )
      | ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('89',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','58','88'])).

thf('90',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('94',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('100',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( X28 = X29 )
      | ( X28 = X30 )
      | ( X28 = X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('102',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('103',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ~ ( zip_tseitin_0 @ X37 @ X33 @ X34 @ X35 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('105',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X33 @ X34 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','113'])).

thf('115',plain,(
    ! [X20: $i,X22: $i] :
      ( ( X20 = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('125',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('128',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['123','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('133',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('134',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','136'])).

thf('138',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['87','89'])).

thf('139',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['60','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aIMwqi1zqP
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 09:53:26 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 1066 iterations in 0.569s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.85/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.03  thf(t67_zfmisc_1, conjecture,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.85/1.03       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i,B:$i]:
% 0.85/1.03        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.85/1.03          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.85/1.03  thf('0', plain,
% 0.85/1.03      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.85/1.03        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('1', plain,
% 0.85/1.03      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.85/1.03       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf(t65_zfmisc_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.85/1.03       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.85/1.03  thf('3', plain,
% 0.85/1.03      (![X46 : $i, X47 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X46 @ (k1_tarski @ X47)) = (X46))
% 0.85/1.03          | (r2_hidden @ X47 @ X46))),
% 0.85/1.03      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.03  thf(t48_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.85/1.03  thf('4', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.85/1.03           = (k3_xboole_0 @ X25 @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.03  thf('5', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.85/1.03          | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.85/1.03  thf(t100_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('6', plain,
% 0.85/1.03      (![X23 : $i, X24 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X23 @ X24)
% 0.85/1.03           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('7', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.85/1.03            = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))
% 0.85/1.03          | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['5', '6'])).
% 0.85/1.03  thf(d3_tarski, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.03  thf('8', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('9', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.85/1.03          | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.85/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.03  thf(d4_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.85/1.03       ( ![D:$i]:
% 0.85/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.03           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.85/1.03  thf('11', plain,
% 0.85/1.03      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X12 @ X11)
% 0.85/1.03          | (r2_hidden @ X12 @ X10)
% 0.85/1.03          | ((X11) != (k3_xboole_0 @ X9 @ X10)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.85/1.03         ((r2_hidden @ X12 @ X10)
% 0.85/1.03          | ~ (r2_hidden @ X12 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['11'])).
% 0.85/1.03  thf('13', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['10', '12'])).
% 0.85/1.03  thf('14', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03          | (r2_hidden @ X1 @ X0)
% 0.85/1.03          | (r2_hidden @ X2 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['9', '13'])).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('condensation', [status(thm)], ['14'])).
% 0.85/1.03  thf(d5_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.85/1.03       ( ![D:$i]:
% 0.85/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.85/1.03  thf('16', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X17)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ X16)
% 0.85/1.03          | ((X17) != (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.85/1.03  thf('17', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X16)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.03  thf('18', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('clc', [status(thm)], ['15', '17'])).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '18'])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('21', plain,
% 0.85/1.03      (((r2_hidden @ sk_A @ sk_B)
% 0.85/1.03        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('22', plain,
% 0.85/1.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('split', [status(esa)], ['21'])).
% 0.85/1.03  thf('23', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('24', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.85/1.03           = (k3_xboole_0 @ X25 @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.03  thf('25', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.85/1.03          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['23', '24'])).
% 0.85/1.03  thf('26', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.85/1.03          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('demod', [status(thm)], ['25', '26'])).
% 0.85/1.03  thf('28', plain,
% 0.85/1.03      (![X46 : $i, X47 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X46 @ (k1_tarski @ X47)) = (X46))
% 0.85/1.03          | (r2_hidden @ X47 @ X46))),
% 0.85/1.03      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 0.85/1.03         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['27', '28'])).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X16)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.03  thf('32', plain,
% 0.85/1.03      ((![X0 : $i]:
% 0.85/1.03          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['30', '31'])).
% 0.85/1.03  thf('33', plain,
% 0.85/1.03      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 0.85/1.03         | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['29', '32'])).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['22', '33'])).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.85/1.03          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('demod', [status(thm)], ['25', '26'])).
% 0.85/1.03  thf('36', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X16)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.03  thf('37', plain,
% 0.85/1.03      ((![X0 : $i]:
% 0.85/1.03          (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.03           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['35', '36'])).
% 0.85/1.03  thf('38', plain,
% 0.85/1.03      ((![X0 : $i]:
% 0.85/1.03          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.85/1.03           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['34', '37'])).
% 0.85/1.03  thf('39', plain,
% 0.85/1.03      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['38'])).
% 0.85/1.03  thf('40', plain,
% 0.85/1.03      ((![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['20', '39'])).
% 0.85/1.03  thf(d10_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.03  thf('41', plain,
% 0.85/1.03      (![X20 : $i, X22 : $i]:
% 0.85/1.03         (((X20) = (X22))
% 0.85/1.03          | ~ (r1_tarski @ X22 @ X20)
% 0.85/1.03          | ~ (r1_tarski @ X20 @ X22))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('42', plain,
% 0.85/1.03      ((![X0 : $i]:
% 0.85/1.03          (~ (r1_tarski @ X0 @ (k1_tarski @ sk_A))
% 0.85/1.03           | ((X0) = (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['40', '41'])).
% 0.85/1.03  thf('43', plain,
% 0.85/1.03      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['19', '42'])).
% 0.85/1.03  thf('44', plain,
% 0.85/1.03      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['22', '33'])).
% 0.85/1.03  thf('45', plain,
% 0.85/1.03      (![X23 : $i, X24 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X23 @ X24)
% 0.85/1.03           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('46', plain,
% 0.85/1.03      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.03          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['44', '45'])).
% 0.85/1.03  thf('47', plain,
% 0.85/1.03      (![X45 : $i, X46 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X45 @ X46)
% 0.85/1.03          | ((k4_xboole_0 @ X46 @ (k1_tarski @ X45)) != (X46)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.03  thf('48', plain,
% 0.85/1.03      (((((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))
% 0.85/1.03         | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['46', '47'])).
% 0.85/1.03  thf('49', plain,
% 0.85/1.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('split', [status(esa)], ['21'])).
% 0.85/1.03  thf('50', plain,
% 0.85/1.03      ((((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['48', '49'])).
% 0.85/1.03  thf('51', plain,
% 0.85/1.03      ((![X0 : $i]: ((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ X0)) != (sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['43', '50'])).
% 0.85/1.03  thf('52', plain,
% 0.85/1.03      ((![X0 : $i]:
% 0.85/1.03          (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) != (sk_B))
% 0.85/1.03           | (r2_hidden @ X0 @ sk_B)))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['7', '51'])).
% 0.85/1.03  thf('53', plain,
% 0.85/1.03      (![X46 : $i, X47 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X46 @ (k1_tarski @ X47)) = (X46))
% 0.85/1.03          | (r2_hidden @ X47 @ X46))),
% 0.85/1.03      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.03  thf('54', plain,
% 0.85/1.03      ((![X0 : $i]: (r2_hidden @ X0 @ sk_B))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('clc', [status(thm)], ['52', '53'])).
% 0.85/1.03  thf('55', plain,
% 0.85/1.03      ((![X0 : $i]: (r2_hidden @ X0 @ sk_B))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('clc', [status(thm)], ['52', '53'])).
% 0.85/1.03  thf(antisymmetry_r2_hidden, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.85/1.03  thf('56', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.85/1.03  thf('57', plain,
% 0.85/1.03      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.85/1.03         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.85/1.03             ((r2_hidden @ sk_A @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['55', '56'])).
% 0.85/1.03  thf('58', plain,
% 0.85/1.03      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.85/1.03       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['54', '57'])).
% 0.85/1.03  thf('59', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.85/1.03      inference('sat_resolution*', [status(thm)], ['2', '58'])).
% 0.85/1.03  thf('60', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.85/1.03  thf('61', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('62', plain,
% 0.85/1.03      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.85/1.03         (((X13) = (k3_xboole_0 @ X9 @ X10))
% 0.85/1.03          | (r2_hidden @ (sk_D @ X13 @ X10 @ X9) @ X10)
% 0.85/1.03          | (r2_hidden @ (sk_D @ X13 @ X10 @ X9) @ X13))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.85/1.03  thf('63', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.85/1.03          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('eq_fact', [status(thm)], ['62'])).
% 0.85/1.03  thf('64', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('clc', [status(thm)], ['15', '17'])).
% 0.85/1.03  thf('65', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X0 @ X0)
% 0.85/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['63', '64'])).
% 0.85/1.03  thf('66', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.03  thf('67', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.85/1.03           = (k3_xboole_0 @ X25 @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.03  thf('68', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X16)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.03  thf('69', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.85/1.03          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['67', '68'])).
% 0.85/1.03  thf('70', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.85/1.03          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['66', '69'])).
% 0.85/1.03  thf('71', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['65', '70'])).
% 0.85/1.03  thf('72', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X18 @ X17)
% 0.85/1.03          | (r2_hidden @ X18 @ X15)
% 0.85/1.03          | ((X17) != (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.85/1.03  thf('73', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.85/1.03         ((r2_hidden @ X18 @ X15)
% 0.85/1.03          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['72'])).
% 0.85/1.03  thf('74', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.85/1.03      inference('clc', [status(thm)], ['71', '73'])).
% 0.85/1.03  thf('75', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) @ X2)),
% 0.85/1.03      inference('sup-', [status(thm)], ['61', '74'])).
% 0.85/1.03  thf('76', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '18'])).
% 0.85/1.03  thf('77', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '18'])).
% 0.85/1.03  thf('78', plain,
% 0.85/1.03      (![X20 : $i, X22 : $i]:
% 0.85/1.03         (((X20) = (X22))
% 0.85/1.03          | ~ (r1_tarski @ X22 @ X20)
% 0.85/1.03          | ~ (r1_tarski @ X20 @ X22))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('79', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.85/1.03          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.85/1.03  thf('80', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['76', '79'])).
% 0.85/1.03  thf('81', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.85/1.03          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.85/1.03  thf('82', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03          | ((X2) = (k4_xboole_0 @ X1 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.85/1.03  thf('83', plain,
% 0.85/1.03      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ X1)
% 0.85/1.03           = (k4_xboole_0 @ X3 @ X3))),
% 0.85/1.03      inference('sup-', [status(thm)], ['75', '82'])).
% 0.85/1.03  thf('84', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['76', '79'])).
% 0.85/1.03  thf('85', plain,
% 0.85/1.03      (![X46 : $i, X47 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X46 @ (k1_tarski @ X47)) = (X46))
% 0.85/1.03          | (r2_hidden @ X47 @ X46))),
% 0.85/1.03      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.03  thf('86', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ X1))
% 0.85/1.03          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['84', '85'])).
% 0.85/1.03  thf('87', plain,
% 0.85/1.03      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.85/1.03         <= (~
% 0.85/1.03             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('split', [status(esa)], ['21'])).
% 0.85/1.03  thf('88', plain,
% 0.85/1.03      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.85/1.03       ((r2_hidden @ sk_A @ sk_B))),
% 0.85/1.03      inference('split', [status(esa)], ['21'])).
% 0.85/1.03  thf('89', plain,
% 0.85/1.03      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sat_resolution*', [status(thm)], ['2', '58', '88'])).
% 0.85/1.03  thf('90', plain,
% 0.85/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.85/1.03  thf('91', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B) != (k1_tarski @ sk_A))
% 0.85/1.03          | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['86', '90'])).
% 0.85/1.03  thf('92', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) != (k1_tarski @ sk_A))
% 0.85/1.03          | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['83', '91'])).
% 0.85/1.03  thf('93', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ X1))
% 0.85/1.03          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['84', '85'])).
% 0.85/1.03  thf('94', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.85/1.03      inference('clc', [status(thm)], ['92', '93'])).
% 0.85/1.03  thf('95', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.85/1.03      inference('clc', [status(thm)], ['92', '93'])).
% 0.85/1.03  thf('96', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X8 @ X9)
% 0.85/1.03          | ~ (r2_hidden @ X8 @ X10)
% 0.85/1.03          | (r2_hidden @ X8 @ X11)
% 0.85/1.03          | ((X11) != (k3_xboole_0 @ X9 @ X10)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.85/1.03  thf('97', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.85/1.03         ((r2_hidden @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.85/1.03          | ~ (r2_hidden @ X8 @ X10)
% 0.85/1.03          | ~ (r2_hidden @ X8 @ X9))),
% 0.85/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.85/1.03  thf('98', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (~ (r2_hidden @ sk_A @ X0)
% 0.85/1.03          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['95', '97'])).
% 0.85/1.03  thf('99', plain,
% 0.85/1.03      ((r2_hidden @ sk_A @ 
% 0.85/1.03        (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['94', '98'])).
% 0.85/1.03  thf(d1_enumset1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.03       ( ![E:$i]:
% 0.85/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.85/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_1, axiom,
% 0.85/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.85/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.85/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.85/1.03  thf('100', plain,
% 0.85/1.03      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.85/1.03         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.85/1.03          | ((X28) = (X29))
% 0.85/1.03          | ((X28) = (X30))
% 0.85/1.03          | ((X28) = (X31)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.85/1.03  thf('101', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf(t69_enumset1, axiom,
% 0.85/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.85/1.03  thf('102', plain,
% 0.85/1.03      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.85/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.03  thf(t70_enumset1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.85/1.03  thf('103', plain,
% 0.85/1.03      (![X40 : $i, X41 : $i]:
% 0.85/1.03         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.85/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.85/1.03  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.85/1.03  thf(zf_stmt_3, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.03       ( ![E:$i]:
% 0.85/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.85/1.03  thf('104', plain,
% 0.85/1.03      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X37 @ X36)
% 0.85/1.03          | ~ (zip_tseitin_0 @ X37 @ X33 @ X34 @ X35)
% 0.85/1.03          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.03  thf('105', plain,
% 0.85/1.03      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 0.85/1.03         (~ (zip_tseitin_0 @ X37 @ X33 @ X34 @ X35)
% 0.85/1.03          | ~ (r2_hidden @ X37 @ (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['104'])).
% 0.85/1.03  thf('106', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.85/1.03          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['103', '105'])).
% 0.85/1.03  thf('107', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.85/1.03          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['102', '106'])).
% 0.85/1.03  thf('108', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.03          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['101', '107'])).
% 0.85/1.03  thf('109', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.03          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.03          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.03          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['100', '108'])).
% 0.85/1.03  thf('110', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.03          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['109'])).
% 0.85/1.03  thf('111', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('112', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X0 @ X1)
% 0.85/1.03          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.03          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['110', '111'])).
% 0.85/1.03  thf('113', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.85/1.03      inference('simplify', [status(thm)], ['112'])).
% 0.85/1.03  thf('114', plain,
% 0.85/1.03      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.85/1.03        (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['99', '113'])).
% 0.85/1.03  thf('115', plain,
% 0.85/1.03      (![X20 : $i, X22 : $i]:
% 0.85/1.03         (((X20) = (X22))
% 0.85/1.03          | ~ (r1_tarski @ X22 @ X20)
% 0.85/1.03          | ~ (r1_tarski @ X20 @ X22))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('116', plain,
% 0.85/1.03      ((~ (r1_tarski @ 
% 0.85/1.03           (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) @ 
% 0.85/1.03           (k1_tarski @ sk_A))
% 0.85/1.03        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.85/1.03            = (k1_tarski @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['114', '115'])).
% 0.85/1.03  thf('117', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('118', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['10', '12'])).
% 0.85/1.03  thf('119', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.03          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['117', '118'])).
% 0.85/1.03  thf('120', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('121', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.85/1.03          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['119', '120'])).
% 0.85/1.03  thf('122', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.85/1.03      inference('simplify', [status(thm)], ['121'])).
% 0.85/1.03  thf('123', plain,
% 0.85/1.03      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.85/1.03         = (k1_tarski @ sk_A))),
% 0.85/1.03      inference('demod', [status(thm)], ['116', '122'])).
% 0.85/1.03  thf('124', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['76', '79'])).
% 0.85/1.03  thf('125', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.85/1.03           = (k3_xboole_0 @ X25 @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.03  thf('126', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03           = (k3_xboole_0 @ X1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['124', '125'])).
% 0.85/1.03  thf('127', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X0 @ X0)
% 0.85/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['63', '64'])).
% 0.85/1.03  thf('128', plain,
% 0.85/1.03      (![X23 : $i, X24 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X23 @ X24)
% 0.85/1.03           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('129', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['127', '128'])).
% 0.85/1.03  thf('130', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03           = (k3_xboole_0 @ X1 @ X1))),
% 0.85/1.03      inference('demod', [status(thm)], ['126', '129'])).
% 0.85/1.03  thf('131', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ X0))
% 0.85/1.03           = (k1_tarski @ sk_A))),
% 0.85/1.03      inference('sup+', [status(thm)], ['123', '130'])).
% 0.85/1.03  thf('132', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.85/1.03          | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.85/1.03  thf('133', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.03  thf('134', plain,
% 0.85/1.03      (![X23 : $i, X24 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X23 @ X24)
% 0.85/1.03           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.03  thf('135', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['133', '134'])).
% 0.85/1.03  thf('136', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.85/1.03            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k4_xboole_0 @ X0 @ X0)))
% 0.85/1.03          | (r2_hidden @ X1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['132', '135'])).
% 0.85/1.03  thf('137', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) = (k1_tarski @ sk_A))
% 0.85/1.03          | (r2_hidden @ sk_A @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['131', '136'])).
% 0.85/1.03  thf('138', plain,
% 0.85/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.85/1.03      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.85/1.03  thf('139', plain,
% 0.85/1.03      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['137', '138'])).
% 0.85/1.03  thf('140', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.85/1.03      inference('simplify', [status(thm)], ['139'])).
% 0.85/1.03  thf('141', plain, ($false), inference('demod', [status(thm)], ['60', '140'])).
% 0.85/1.03  
% 0.85/1.03  % SZS output end Refutation
% 0.85/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
