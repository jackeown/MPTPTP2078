%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qSNXdWW4IQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:05 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 857 expanded)
%              Number of leaves         :   24 ( 246 expanded)
%              Depth                    :   24
%              Number of atoms          : 1125 (9180 expanded)
%              Number of equality atoms :   61 ( 621 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t173_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_relat_1])).

thf('0',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k2_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X21 @ X18 ) @ ( sk_C_1 @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('13',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X23 @ X24 )
        = ( k10_relat_1 @ X23 @ ( k3_xboole_0 @ ( k2_relat_1 @ X23 ) @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('33',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ sk_A )
        = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_E_1 @ X13 @ X9 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_E_1 @ X13 @ X9 @ X10 ) ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E_1 @ X0 @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E_1 @ X0 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_E_1 @ ( sk_C_1 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('43',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) @ sk_A @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
        | ( r2_hidden @ ( sk_E_1 @ X0 @ sk_A @ sk_B ) @ sk_A )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
        | ( r2_hidden @ ( sk_E_1 @ X0 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) @ sk_A @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
          = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
      | ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','62'])).

thf('64',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('66',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','69','70'])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('76',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X12
       != ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X10 )
      | ( r2_hidden @ X14 @ ( k10_relat_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','69'])).

thf('88',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['85','88'])).

thf('90',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['85','88'])).

thf('91',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sup-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qSNXdWW4IQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.22/2.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.44  % Solved by: fo/fo7.sh
% 2.22/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.44  % done 1494 iterations in 1.987s
% 2.22/2.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.44  % SZS output start Refutation
% 2.22/2.44  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.44  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.22/2.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.22/2.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.22/2.44  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.22/2.44  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.22/2.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.22/2.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.22/2.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.22/2.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.22/2.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.22/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.22/2.44  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.22/2.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.22/2.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.22/2.44  thf(t173_relat_1, conjecture,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 2.22/2.44         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.22/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.44    (~( ![A:$i,B:$i]:
% 2.22/2.44        ( ( v1_relat_1 @ B ) =>
% 2.22/2.44          ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 2.22/2.44            ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )),
% 2.22/2.44    inference('cnf.neg', [status(esa)], [t173_relat_1])).
% 2.22/2.44  thf('0', plain,
% 2.22/2.44      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.22/2.44        | ((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('1', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 2.22/2.44         <= ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 2.22/2.44      inference('split', [status(esa)], ['0'])).
% 2.22/2.44  thf('2', plain,
% 2.22/2.44      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.22/2.44        | ((k10_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('3', plain,
% 2.22/2.44      (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)) | 
% 2.22/2.44       ~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 2.22/2.44      inference('split', [status(esa)], ['2'])).
% 2.22/2.44  thf(t60_relat_1, axiom,
% 2.22/2.44    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.22/2.44     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.22/2.44  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.22/2.44  thf(d5_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.22/2.44       ( ![C:$i]:
% 2.22/2.44         ( ( r2_hidden @ C @ B ) <=>
% 2.22/2.44           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 2.22/2.44  thf('5', plain,
% 2.22/2.44      (![X18 : $i, X21 : $i]:
% 2.22/2.44         (((X21) = (k2_relat_1 @ X18))
% 2.22/2.44          | (r2_hidden @ 
% 2.22/2.44             (k4_tarski @ (sk_D_1 @ X21 @ X18) @ (sk_C_1 @ X21 @ X18)) @ X18)
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X21 @ X18) @ X21))),
% 2.22/2.44      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.22/2.44  thf('6', plain,
% 2.22/2.44      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.22/2.44         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 2.22/2.44          | (r2_hidden @ X17 @ X19)
% 2.22/2.44          | ((X19) != (k2_relat_1 @ X18)))),
% 2.22/2.44      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.22/2.44  thf('7', plain,
% 2.22/2.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.44         ((r2_hidden @ X17 @ (k2_relat_1 @ X18))
% 2.22/2.44          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 2.22/2.44      inference('simplify', [status(thm)], ['6'])).
% 2.22/2.44  thf('8', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 2.22/2.44          | ((X1) = (k2_relat_1 @ X0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['5', '7'])).
% 2.22/2.44  thf('9', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.22/2.44          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('sup+', [status(thm)], ['4', '8'])).
% 2.22/2.44  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.22/2.44  thf('11', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('demod', [status(thm)], ['9', '10'])).
% 2.22/2.44  thf('12', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('demod', [status(thm)], ['9', '10'])).
% 2.22/2.44  thf(t3_xboole_0, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.22/2.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.22/2.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.22/2.44            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.22/2.44  thf('13', plain,
% 2.22/2.44      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X5 @ X3)
% 2.22/2.44          | ~ (r2_hidden @ X5 @ X6)
% 2.22/2.44          | ~ (r1_xboole_0 @ X3 @ X6))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('14', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 2.22/2.44          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 2.22/2.44      inference('sup-', [status(thm)], ['12', '13'])).
% 2.22/2.44  thf(t2_boole, axiom,
% 2.22/2.44    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.22/2.44  thf('15', plain,
% 2.22/2.44      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.44      inference('cnf', [status(esa)], [t2_boole])).
% 2.22/2.44  thf(d7_xboole_0, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.22/2.44       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.22/2.44  thf('16', plain,
% 2.22/2.44      (![X0 : $i, X2 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 2.22/2.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.22/2.44  thf('17', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['15', '16'])).
% 2.22/2.44  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.22/2.44      inference('simplify', [status(thm)], ['17'])).
% 2.22/2.44  thf('19', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('20', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('21', plain,
% 2.22/2.44      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X5 @ X3)
% 2.22/2.44          | ~ (r2_hidden @ X5 @ X6)
% 2.22/2.44          | ~ (r1_xboole_0 @ X3 @ X6))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('22', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X0 @ X1)
% 2.22/2.44          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.22/2.44          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.22/2.44      inference('sup-', [status(thm)], ['20', '21'])).
% 2.22/2.44  thf('23', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X0 @ X1)
% 2.22/2.44          | ~ (r1_xboole_0 @ X0 @ X0)
% 2.22/2.44          | (r1_xboole_0 @ X0 @ X1))),
% 2.22/2.44      inference('sup-', [status(thm)], ['19', '22'])).
% 2.22/2.44  thf('24', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.22/2.44      inference('simplify', [status(thm)], ['23'])).
% 2.22/2.44  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.22/2.44      inference('sup-', [status(thm)], ['18', '24'])).
% 2.22/2.44  thf('26', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 2.22/2.44      inference('demod', [status(thm)], ['14', '25'])).
% 2.22/2.44  thf('27', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | ((X0) = (k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['11', '26'])).
% 2.22/2.44  thf('28', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         (((X0) = (k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('simplify', [status(thm)], ['27'])).
% 2.22/2.44  thf('29', plain,
% 2.22/2.44      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('split', [status(esa)], ['0'])).
% 2.22/2.44  thf('30', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.22/2.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.22/2.44  thf('31', plain,
% 2.22/2.44      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['29', '30'])).
% 2.22/2.44  thf(t168_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( k10_relat_1 @ B @ A ) =
% 2.22/2.44         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 2.22/2.44  thf('32', plain,
% 2.22/2.44      (![X23 : $i, X24 : $i]:
% 2.22/2.44         (((k10_relat_1 @ X23 @ X24)
% 2.22/2.44            = (k10_relat_1 @ X23 @ (k3_xboole_0 @ (k2_relat_1 @ X23) @ X24)))
% 2.22/2.44          | ~ (v1_relat_1 @ X23))),
% 2.22/2.44      inference('cnf', [status(esa)], [t168_relat_1])).
% 2.22/2.44  thf('33', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ sk_B @ k1_xboole_0))
% 2.22/2.44         | ~ (v1_relat_1 @ sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup+', [status(thm)], ['31', '32'])).
% 2.22/2.44  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('35', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ sk_B @ k1_xboole_0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.22/2.44  thf(d14_relat_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ A ) =>
% 2.22/2.44       ( ![B:$i,C:$i]:
% 2.22/2.44         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 2.22/2.44           ( ![D:$i]:
% 2.22/2.44             ( ( r2_hidden @ D @ C ) <=>
% 2.22/2.44               ( ?[E:$i]:
% 2.22/2.44                 ( ( r2_hidden @ E @ B ) & 
% 2.22/2.44                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 2.22/2.44  thf('36', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 2.22/2.44         (((X12) != (k10_relat_1 @ X10 @ X9))
% 2.22/2.44          | (r2_hidden @ (k4_tarski @ X13 @ (sk_E_1 @ X13 @ X9 @ X10)) @ X10)
% 2.22/2.44          | ~ (r2_hidden @ X13 @ X12)
% 2.22/2.44          | ~ (v1_relat_1 @ X10))),
% 2.22/2.44      inference('cnf', [status(esa)], [d14_relat_1])).
% 2.22/2.44  thf('37', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X13 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X10)
% 2.22/2.44          | ~ (r2_hidden @ X13 @ (k10_relat_1 @ X10 @ X9))
% 2.22/2.44          | (r2_hidden @ (k4_tarski @ X13 @ (sk_E_1 @ X13 @ X9 @ X10)) @ X10))),
% 2.22/2.44      inference('simplify', [status(thm)], ['36'])).
% 2.22/2.44  thf('38', plain,
% 2.22/2.44      ((![X0 : $i]:
% 2.22/2.44          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 2.22/2.44           | (r2_hidden @ (k4_tarski @ X0 @ (sk_E_1 @ X0 @ sk_A @ sk_B)) @ sk_B)
% 2.22/2.44           | ~ (v1_relat_1 @ sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['35', '37'])).
% 2.22/2.44  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('40', plain,
% 2.22/2.44      ((![X0 : $i]:
% 2.22/2.44          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 2.22/2.44           | (r2_hidden @ (k4_tarski @ X0 @ (sk_E_1 @ X0 @ sk_A @ sk_B)) @ sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['38', '39'])).
% 2.22/2.44  thf('41', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44         | (r2_hidden @ 
% 2.22/2.44            (k4_tarski @ 
% 2.22/2.44             (sk_C_1 @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.22/2.44             (sk_E_1 @ 
% 2.22/2.44              (sk_C_1 @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.22/2.44              sk_A @ sk_B)) @ 
% 2.22/2.44            sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['28', '40'])).
% 2.22/2.44  thf('42', plain,
% 2.22/2.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.44         ((r2_hidden @ X17 @ (k2_relat_1 @ X18))
% 2.22/2.44          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 2.22/2.44      inference('simplify', [status(thm)], ['6'])).
% 2.22/2.44  thf('43', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44         | (r2_hidden @ 
% 2.22/2.44            (sk_E_1 @ 
% 2.22/2.44             (sk_C_1 @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.22/2.44             sk_A @ sk_B) @ 
% 2.22/2.44            (k2_relat_1 @ sk_B))))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['41', '42'])).
% 2.22/2.44  thf('44', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         (((X0) = (k1_xboole_0))
% 2.22/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 2.22/2.44      inference('simplify', [status(thm)], ['27'])).
% 2.22/2.44  thf('45', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ sk_B @ k1_xboole_0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.22/2.44  thf('46', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 2.22/2.44         (((X12) != (k10_relat_1 @ X10 @ X9))
% 2.22/2.44          | (r2_hidden @ (sk_E_1 @ X13 @ X9 @ X10) @ X9)
% 2.22/2.44          | ~ (r2_hidden @ X13 @ X12)
% 2.22/2.44          | ~ (v1_relat_1 @ X10))),
% 2.22/2.44      inference('cnf', [status(esa)], [d14_relat_1])).
% 2.22/2.44  thf('47', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X13 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X10)
% 2.22/2.44          | ~ (r2_hidden @ X13 @ (k10_relat_1 @ X10 @ X9))
% 2.22/2.44          | (r2_hidden @ (sk_E_1 @ X13 @ X9 @ X10) @ X9))),
% 2.22/2.44      inference('simplify', [status(thm)], ['46'])).
% 2.22/2.44  thf('48', plain,
% 2.22/2.44      ((![X0 : $i]:
% 2.22/2.44          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 2.22/2.44           | (r2_hidden @ (sk_E_1 @ X0 @ sk_A @ sk_B) @ sk_A)
% 2.22/2.44           | ~ (v1_relat_1 @ sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['45', '47'])).
% 2.22/2.44  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('50', plain,
% 2.22/2.44      ((![X0 : $i]:
% 2.22/2.44          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B @ k1_xboole_0))
% 2.22/2.44           | (r2_hidden @ (sk_E_1 @ X0 @ sk_A @ sk_B) @ sk_A)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['48', '49'])).
% 2.22/2.44  thf('51', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44         | (r2_hidden @ 
% 2.22/2.44            (sk_E_1 @ 
% 2.22/2.44             (sk_C_1 @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.22/2.44             sk_A @ sk_B) @ 
% 2.22/2.44            sk_A)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['44', '50'])).
% 2.22/2.44  thf('52', plain,
% 2.22/2.44      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X5 @ X3)
% 2.22/2.44          | ~ (r2_hidden @ X5 @ X6)
% 2.22/2.44          | ~ (r1_xboole_0 @ X3 @ X6))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('53', plain,
% 2.22/2.44      ((![X0 : $i]:
% 2.22/2.44          (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44           | ~ (r1_xboole_0 @ sk_A @ X0)
% 2.22/2.44           | ~ (r2_hidden @ 
% 2.22/2.44                (sk_E_1 @ 
% 2.22/2.44                 (sk_C_1 @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.22/2.44                 sk_A @ sk_B) @ 
% 2.22/2.44                X0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['51', '52'])).
% 2.22/2.44  thf('54', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44         | ~ (r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 2.22/2.44         | ((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['43', '53'])).
% 2.22/2.44  thf('55', plain,
% 2.22/2.44      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('split', [status(esa)], ['0'])).
% 2.22/2.44  thf('56', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('57', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('58', plain,
% 2.22/2.44      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X5 @ X3)
% 2.22/2.44          | ~ (r2_hidden @ X5 @ X6)
% 2.22/2.44          | ~ (r1_xboole_0 @ X3 @ X6))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('59', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X1 @ X0)
% 2.22/2.44          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.22/2.44          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 2.22/2.44      inference('sup-', [status(thm)], ['57', '58'])).
% 2.22/2.44  thf('60', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X0 @ X1)
% 2.22/2.44          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.22/2.44          | (r1_xboole_0 @ X0 @ X1))),
% 2.22/2.44      inference('sup-', [status(thm)], ['56', '59'])).
% 2.22/2.44  thf('61', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.22/2.44      inference('simplify', [status(thm)], ['60'])).
% 2.22/2.44  thf('62', plain,
% 2.22/2.44      (((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['55', '61'])).
% 2.22/2.44  thf('63', plain,
% 2.22/2.44      (((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 2.22/2.44         | ((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['54', '62'])).
% 2.22/2.44  thf('64', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('simplify', [status(thm)], ['63'])).
% 2.22/2.44  thf('65', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ sk_B @ k1_xboole_0)))
% 2.22/2.44         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.22/2.44  thf('66', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 2.22/2.44         <= (~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 2.22/2.44      inference('split', [status(esa)], ['2'])).
% 2.22/2.44  thf('67', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0)))
% 2.22/2.44         <= (~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 2.22/2.44             ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['65', '66'])).
% 2.22/2.44  thf('68', plain,
% 2.22/2.44      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.22/2.44         <= (~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 2.22/2.44             ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['64', '67'])).
% 2.22/2.44  thf('69', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 2.22/2.44       ~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 2.22/2.44      inference('simplify', [status(thm)], ['68'])).
% 2.22/2.44  thf('70', plain,
% 2.22/2.44      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 2.22/2.44       ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 2.22/2.44      inference('split', [status(esa)], ['0'])).
% 2.22/2.44  thf('71', plain, ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 2.22/2.44      inference('sat_resolution*', [status(thm)], ['3', '69', '70'])).
% 2.22/2.44  thf('72', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 2.22/2.44      inference('simpl_trail', [status(thm)], ['1', '71'])).
% 2.22/2.44  thf('73', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('74', plain,
% 2.22/2.44      (![X3 : $i, X4 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('75', plain,
% 2.22/2.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X20 @ X19)
% 2.22/2.44          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X20 @ X18) @ X20) @ X18)
% 2.22/2.44          | ((X19) != (k2_relat_1 @ X18)))),
% 2.22/2.44      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.22/2.44  thf('76', plain,
% 2.22/2.44      (![X18 : $i, X20 : $i]:
% 2.22/2.44         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X20 @ X18) @ X20) @ X18)
% 2.22/2.44          | ~ (r2_hidden @ X20 @ (k2_relat_1 @ X18)))),
% 2.22/2.44      inference('simplify', [status(thm)], ['75'])).
% 2.22/2.44  thf('77', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 2.22/2.44          | (r2_hidden @ 
% 2.22/2.44             (k4_tarski @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.22/2.44              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 2.22/2.44             X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['74', '76'])).
% 2.22/2.44  thf('78', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 2.22/2.44         (((X12) != (k10_relat_1 @ X10 @ X9))
% 2.22/2.44          | (r2_hidden @ X14 @ X12)
% 2.22/2.44          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X10)
% 2.22/2.44          | ~ (r2_hidden @ X15 @ X9)
% 2.22/2.44          | ~ (v1_relat_1 @ X10))),
% 2.22/2.44      inference('cnf', [status(esa)], [d14_relat_1])).
% 2.22/2.44  thf('79', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X14 : $i, X15 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X10)
% 2.22/2.44          | ~ (r2_hidden @ X15 @ X9)
% 2.22/2.44          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X10)
% 2.22/2.44          | (r2_hidden @ X14 @ (k10_relat_1 @ X10 @ X9)))),
% 2.22/2.44      inference('simplify', [status(thm)], ['78'])).
% 2.22/2.44  thf('80', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 2.22/2.44          | (r2_hidden @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.22/2.44             (k10_relat_1 @ X0 @ X2))
% 2.22/2.44          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 2.22/2.44          | ~ (v1_relat_1 @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['77', '79'])).
% 2.22/2.44  thf('81', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | (r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ X1)) @ X1) @ 
% 2.22/2.44             (k10_relat_1 @ X1 @ X0))
% 2.22/2.44          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['73', '80'])).
% 2.22/2.44  thf('82', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ X1)) @ X1) @ 
% 2.22/2.44           (k10_relat_1 @ X1 @ X0))
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 2.22/2.44      inference('simplify', [status(thm)], ['81'])).
% 2.22/2.44  thf('83', plain,
% 2.22/2.44      (((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 2.22/2.44         k1_xboole_0)
% 2.22/2.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.22/2.44        | ~ (v1_relat_1 @ sk_B))),
% 2.22/2.44      inference('sup+', [status(thm)], ['72', '82'])).
% 2.22/2.44  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('85', plain,
% 2.22/2.44      (((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 2.22/2.44         k1_xboole_0)
% 2.22/2.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['83', '84'])).
% 2.22/2.44  thf('86', plain,
% 2.22/2.44      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 2.22/2.44         <= (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 2.22/2.44      inference('split', [status(esa)], ['2'])).
% 2.22/2.44  thf('87', plain, (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 2.22/2.44      inference('sat_resolution*', [status(thm)], ['3', '69'])).
% 2.22/2.44  thf('88', plain, (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 2.22/2.44      inference('simpl_trail', [status(thm)], ['86', '87'])).
% 2.22/2.44  thf('89', plain,
% 2.22/2.44      ((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 2.22/2.44        k1_xboole_0)),
% 2.22/2.44      inference('clc', [status(thm)], ['85', '88'])).
% 2.22/2.44  thf('90', plain,
% 2.22/2.44      ((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 2.22/2.44        k1_xboole_0)),
% 2.22/2.44      inference('clc', [status(thm)], ['85', '88'])).
% 2.22/2.44  thf('91', plain,
% 2.22/2.44      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.22/2.44         (~ (r2_hidden @ X5 @ X3)
% 2.22/2.44          | ~ (r2_hidden @ X5 @ X6)
% 2.22/2.44          | ~ (r1_xboole_0 @ X3 @ X6))),
% 2.22/2.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.22/2.44  thf('92', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 2.22/2.44          | ~ (r2_hidden @ 
% 2.22/2.44               (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['90', '91'])).
% 2.22/2.44  thf('93', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.22/2.44      inference('sup-', [status(thm)], ['18', '24'])).
% 2.22/2.44  thf('94', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ~ (r2_hidden @ 
% 2.22/2.44            (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ X0)),
% 2.22/2.44      inference('demod', [status(thm)], ['92', '93'])).
% 2.22/2.44  thf('95', plain, ($false), inference('sup-', [status(thm)], ['89', '94'])).
% 2.22/2.44  
% 2.22/2.44  % SZS output end Refutation
% 2.22/2.44  
% 2.28/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
