%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oCnLMCOj2T

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:11 EST 2020

% Result     : Theorem 20.93s
% Output     : Refutation 20.93s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 140 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  830 (1238 expanded)
%              Number of equality atoms :   39 (  63 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) ) )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) ) )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
        = X0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('60',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oCnLMCOj2T
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 20.93/21.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.93/21.10  % Solved by: fo/fo7.sh
% 20.93/21.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.93/21.10  % done 32437 iterations in 20.656s
% 20.93/21.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.93/21.10  % SZS output start Refutation
% 20.93/21.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.93/21.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 20.93/21.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.93/21.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.93/21.10  thf(sk_A_type, type, sk_A: $i).
% 20.93/21.10  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 20.93/21.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 20.93/21.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.93/21.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.93/21.10  thf(sk_B_type, type, sk_B: $i).
% 20.93/21.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.93/21.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.93/21.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 20.93/21.10  thf(t95_relat_1, conjecture,
% 20.93/21.10    (![A:$i,B:$i]:
% 20.93/21.10     ( ( v1_relat_1 @ B ) =>
% 20.93/21.10       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 20.93/21.10         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 20.93/21.10  thf(zf_stmt_0, negated_conjecture,
% 20.93/21.10    (~( ![A:$i,B:$i]:
% 20.93/21.10        ( ( v1_relat_1 @ B ) =>
% 20.93/21.10          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 20.93/21.10            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 20.93/21.10    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 20.93/21.10  thf('0', plain,
% 20.93/21.10      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 20.93/21.10        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 20.93/21.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.10  thf('1', plain,
% 20.93/21.10      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 20.93/21.10       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 20.93/21.10      inference('split', [status(esa)], ['0'])).
% 20.93/21.10  thf('2', plain,
% 20.93/21.10      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 20.93/21.10        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 20.93/21.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.10  thf('3', plain,
% 20.93/21.10      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 20.93/21.10         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.10      inference('split', [status(esa)], ['2'])).
% 20.93/21.10  thf(t3_xboole_0, axiom,
% 20.93/21.10    (![A:$i,B:$i]:
% 20.93/21.10     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 20.93/21.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 20.93/21.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 20.93/21.10            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 20.93/21.10  thf('4', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('5', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf(t86_relat_1, axiom,
% 20.93/21.10    (![A:$i,B:$i,C:$i]:
% 20.93/21.10     ( ( v1_relat_1 @ C ) =>
% 20.93/21.10       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 20.93/21.10         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 20.93/21.10  thf('6', plain,
% 20.93/21.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X22 @ X23)
% 20.93/21.10          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X24))
% 20.93/21.10          | (r2_hidden @ X22 @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X23)))
% 20.93/21.10          | ~ (v1_relat_1 @ X24))),
% 20.93/21.10      inference('cnf', [status(esa)], [t86_relat_1])).
% 20.93/21.10  thf('7', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 20.93/21.10          | ~ (v1_relat_1 @ X0)
% 20.93/21.10          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 20.93/21.10             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 20.93/21.10          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 20.93/21.10      inference('sup-', [status(thm)], ['5', '6'])).
% 20.93/21.10  thf('8', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 20.93/21.10          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 20.93/21.10             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 20.93/21.10          | ~ (v1_relat_1 @ X1)
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 20.93/21.10      inference('sup-', [status(thm)], ['4', '7'])).
% 20.93/21.10  thf('9', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i]:
% 20.93/21.10         (~ (v1_relat_1 @ X1)
% 20.93/21.10          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 20.93/21.10             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 20.93/21.10      inference('simplify', [status(thm)], ['8'])).
% 20.93/21.10  thf('10', plain,
% 20.93/21.10      ((((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 20.93/21.10          (k1_relat_1 @ k1_xboole_0))
% 20.93/21.10         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 20.93/21.10         | ~ (v1_relat_1 @ sk_B)))
% 20.93/21.10         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.10      inference('sup+', [status(thm)], ['3', '9'])).
% 20.93/21.10  thf(t60_relat_1, axiom,
% 20.93/21.10    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 20.93/21.10     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 20.93/21.10  thf('11', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 20.93/21.10      inference('cnf', [status(esa)], [t60_relat_1])).
% 20.93/21.10  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 20.93/21.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.10  thf('13', plain,
% 20.93/21.10      ((((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 20.93/21.10         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 20.93/21.10         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.10      inference('demod', [status(thm)], ['10', '11', '12'])).
% 20.93/21.10  thf(t2_boole, axiom,
% 20.93/21.10    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 20.93/21.10  thf('14', plain,
% 20.93/21.10      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 20.93/21.10      inference('cnf', [status(esa)], [t2_boole])).
% 20.93/21.10  thf(t4_xboole_0, axiom,
% 20.93/21.10    (![A:$i,B:$i]:
% 20.93/21.10     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 20.93/21.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 20.93/21.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 20.93/21.10            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 20.93/21.10  thf('15', plain,
% 20.93/21.10      (![X7 : $i, X9 : $i, X10 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 20.93/21.10          | ~ (r1_xboole_0 @ X7 @ X10))),
% 20.93/21.10      inference('cnf', [status(esa)], [t4_xboole_0])).
% 20.93/21.10  thf('16', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 20.93/21.10      inference('sup-', [status(thm)], ['14', '15'])).
% 20.93/21.10  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 20.93/21.10  thf('17', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 20.93/21.10      inference('cnf', [status(esa)], [t65_xboole_1])).
% 20.93/21.10  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 20.93/21.10      inference('demod', [status(thm)], ['16', '17'])).
% 20.93/21.10  thf('19', plain,
% 20.93/21.10      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 20.93/21.10         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.10      inference('clc', [status(thm)], ['13', '18'])).
% 20.93/21.10  thf('20', plain,
% 20.93/21.10      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 20.93/21.10         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('split', [status(esa)], ['0'])).
% 20.93/21.10  thf('21', plain,
% 20.93/21.10      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 20.93/21.10       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['19', '20'])).
% 20.93/21.10  thf('22', plain,
% 20.93/21.10      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 20.93/21.10       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 20.93/21.10      inference('split', [status(esa)], ['2'])).
% 20.93/21.10  thf(dt_k7_relat_1, axiom,
% 20.93/21.10    (![A:$i,B:$i]:
% 20.93/21.10     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 20.93/21.10  thf('23', plain,
% 20.93/21.10      (![X19 : $i, X20 : $i]:
% 20.93/21.10         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 20.93/21.10      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 20.93/21.10  thf('24', plain,
% 20.93/21.10      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('split', [status(esa)], ['2'])).
% 20.93/21.10  thf(symmetry_r1_xboole_0, axiom,
% 20.93/21.10    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 20.93/21.10  thf('25', plain,
% 20.93/21.10      (![X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 20.93/21.10      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 20.93/21.10  thf('26', plain,
% 20.93/21.10      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['24', '25'])).
% 20.93/21.10  thf('27', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('28', plain,
% 20.93/21.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X22 @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X23)))
% 20.93/21.10          | (r2_hidden @ X22 @ (k1_relat_1 @ X24))
% 20.93/21.10          | ~ (v1_relat_1 @ X24))),
% 20.93/21.10      inference('cnf', [status(esa)], [t86_relat_1])).
% 20.93/21.10  thf('29', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 20.93/21.10          | ~ (v1_relat_1 @ X1)
% 20.93/21.10          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 20.93/21.10             (k1_relat_1 @ X1)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['27', '28'])).
% 20.93/21.10  thf('30', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('31', plain,
% 20.93/21.10      (![X3 : $i, X5 : $i, X6 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X5 @ X3)
% 20.93/21.10          | ~ (r2_hidden @ X5 @ X6)
% 20.93/21.10          | ~ (r1_xboole_0 @ X3 @ X6))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('32', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X1 @ X0)
% 20.93/21.10          | ~ (r1_xboole_0 @ X0 @ X2)
% 20.93/21.10          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 20.93/21.10      inference('sup-', [status(thm)], ['30', '31'])).
% 20.93/21.10  thf('33', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         (~ (v1_relat_1 @ X0)
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 20.93/21.10          | ~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2))),
% 20.93/21.10      inference('sup-', [status(thm)], ['29', '32'])).
% 20.93/21.10  thf('34', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         (~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 20.93/21.10          | ~ (v1_relat_1 @ X0))),
% 20.93/21.10      inference('simplify', [status(thm)], ['33'])).
% 20.93/21.10  thf('35', plain,
% 20.93/21.10      ((![X0 : $i]:
% 20.93/21.10          (~ (v1_relat_1 @ sk_B)
% 20.93/21.10           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A)))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['26', '34'])).
% 20.93/21.10  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 20.93/21.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.10  thf('37', plain,
% 20.93/21.10      ((![X0 : $i]:
% 20.93/21.10          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('demod', [status(thm)], ['35', '36'])).
% 20.93/21.10  thf('38', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('39', plain,
% 20.93/21.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X22 @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X23)))
% 20.93/21.10          | (r2_hidden @ X22 @ X23)
% 20.93/21.10          | ~ (v1_relat_1 @ X24))),
% 20.93/21.10      inference('cnf', [status(esa)], [t86_relat_1])).
% 20.93/21.10  thf('40', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 20.93/21.10          | ~ (v1_relat_1 @ X1)
% 20.93/21.10          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 20.93/21.10             X0))),
% 20.93/21.10      inference('sup-', [status(thm)], ['38', '39'])).
% 20.93/21.10  thf('41', plain,
% 20.93/21.10      (![X3 : $i, X4 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('42', plain,
% 20.93/21.10      (![X3 : $i, X5 : $i, X6 : $i]:
% 20.93/21.10         (~ (r2_hidden @ X5 @ X3)
% 20.93/21.10          | ~ (r2_hidden @ X5 @ X6)
% 20.93/21.10          | ~ (r1_xboole_0 @ X3 @ X6))),
% 20.93/21.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 20.93/21.10  thf('43', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X0 @ X1)
% 20.93/21.10          | ~ (r1_xboole_0 @ X0 @ X2)
% 20.93/21.10          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 20.93/21.10      inference('sup-', [status(thm)], ['41', '42'])).
% 20.93/21.10  thf('44', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         (~ (v1_relat_1 @ X1)
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 20.93/21.10          | ~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 20.93/21.10      inference('sup-', [status(thm)], ['40', '43'])).
% 20.93/21.10  thf('45', plain,
% 20.93/21.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.93/21.10         (~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 20.93/21.10          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 20.93/21.10          | ~ (v1_relat_1 @ X1))),
% 20.93/21.10      inference('simplify', [status(thm)], ['44'])).
% 20.93/21.10  thf('46', plain,
% 20.93/21.10      ((![X0 : $i]:
% 20.93/21.10          (~ (v1_relat_1 @ sk_B)
% 20.93/21.10           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0)))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['37', '45'])).
% 20.93/21.10  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 20.93/21.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.10  thf('48', plain,
% 20.93/21.10      ((![X0 : $i]:
% 20.93/21.10          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('demod', [status(thm)], ['46', '47'])).
% 20.93/21.10  thf('49', plain,
% 20.93/21.10      (![X1 : $i, X2 : $i]:
% 20.93/21.10         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 20.93/21.10      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 20.93/21.10  thf('50', plain,
% 20.93/21.10      ((![X0 : $i]:
% 20.93/21.10          (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 20.93/21.10         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.10      inference('sup-', [status(thm)], ['48', '49'])).
% 20.93/21.10  thf(t83_xboole_1, axiom,
% 20.93/21.11    (![A:$i,B:$i]:
% 20.93/21.11     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 20.93/21.11  thf('51', plain,
% 20.93/21.11      (![X16 : $i, X17 : $i]:
% 20.93/21.11         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 20.93/21.11      inference('cnf', [status(esa)], [t83_xboole_1])).
% 20.93/21.11  thf('52', plain,
% 20.93/21.11      ((![X0 : $i]:
% 20.93/21.11          ((k4_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 20.93/21.11            = (X0)))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('sup-', [status(thm)], ['50', '51'])).
% 20.93/21.11  thf(t3_boole, axiom,
% 20.93/21.11    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 20.93/21.11  thf('53', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 20.93/21.11      inference('cnf', [status(esa)], [t3_boole])).
% 20.93/21.11  thf(t48_xboole_1, axiom,
% 20.93/21.11    (![A:$i,B:$i]:
% 20.93/21.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 20.93/21.11  thf('54', plain,
% 20.93/21.11      (![X13 : $i, X14 : $i]:
% 20.93/21.11         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 20.93/21.11           = (k3_xboole_0 @ X13 @ X14))),
% 20.93/21.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.93/21.11  thf('55', plain,
% 20.93/21.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 20.93/21.11      inference('sup+', [status(thm)], ['53', '54'])).
% 20.93/21.11  thf('56', plain,
% 20.93/21.11      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 20.93/21.11      inference('cnf', [status(esa)], [t2_boole])).
% 20.93/21.11  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 20.93/21.11      inference('demod', [status(thm)], ['55', '56'])).
% 20.93/21.11  thf('58', plain,
% 20.93/21.11      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('sup+', [status(thm)], ['52', '57'])).
% 20.93/21.11  thf(fc8_relat_1, axiom,
% 20.93/21.11    (![A:$i]:
% 20.93/21.11     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 20.93/21.11       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 20.93/21.11  thf('59', plain,
% 20.93/21.11      (![X21 : $i]:
% 20.93/21.11         (~ (v1_xboole_0 @ (k1_relat_1 @ X21))
% 20.93/21.11          | ~ (v1_relat_1 @ X21)
% 20.93/21.11          | (v1_xboole_0 @ X21))),
% 20.93/21.11      inference('cnf', [status(esa)], [fc8_relat_1])).
% 20.93/21.11  thf('60', plain,
% 20.93/21.11      (((~ (v1_xboole_0 @ k1_xboole_0)
% 20.93/21.11         | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 20.93/21.11         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('sup-', [status(thm)], ['58', '59'])).
% 20.93/21.11  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 20.93/21.11  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.93/21.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 20.93/21.11  thf('62', plain,
% 20.93/21.11      ((((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 20.93/21.11         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('demod', [status(thm)], ['60', '61'])).
% 20.93/21.11  thf('63', plain,
% 20.93/21.11      (((~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('sup-', [status(thm)], ['23', '62'])).
% 20.93/21.11  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 20.93/21.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.93/21.11  thf('65', plain,
% 20.93/21.11      (((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))
% 20.93/21.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 20.93/21.11      inference('demod', [status(thm)], ['63', '64'])).
% 20.93/21.11  thf(l13_xboole_0, axiom,
% 20.93/21.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 20.93/21.11  thf('66', plain,
% 20.93/21.11      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.93/21.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.93/21.11  thf('67', plain,
% 20.93/21.11      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 20.93/21.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 20.93/21.11  thf('68', plain,
% 20.93/21.11      (![X0 : $i, X1 : $i]:
% 20.93/21.11         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 20.93/21.11      inference('sup+', [status(thm)], ['66', '67'])).
% 20.93/21.11  thf('69', plain,
% 20.93/21.11      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 20.93/21.11         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.11      inference('split', [status(esa)], ['0'])).
% 20.93/21.11  thf('70', plain,
% 20.93/21.11      ((![X0 : $i]:
% 20.93/21.11          (((X0) != (k1_xboole_0))
% 20.93/21.11           | ~ (v1_xboole_0 @ X0)
% 20.93/21.11           | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))))
% 20.93/21.11         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.11      inference('sup-', [status(thm)], ['68', '69'])).
% 20.93/21.11  thf('71', plain,
% 20.93/21.11      (((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 20.93/21.11         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 20.93/21.11         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.11      inference('simplify', [status(thm)], ['70'])).
% 20.93/21.11  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 20.93/21.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 20.93/21.11  thf('73', plain,
% 20.93/21.11      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))
% 20.93/21.11         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 20.93/21.11      inference('simplify_reflect+', [status(thm)], ['71', '72'])).
% 20.93/21.11  thf('74', plain,
% 20.93/21.11      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 20.93/21.11       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 20.93/21.11      inference('sup-', [status(thm)], ['65', '73'])).
% 20.93/21.11  thf('75', plain, ($false),
% 20.93/21.11      inference('sat_resolution*', [status(thm)], ['1', '21', '22', '74'])).
% 20.93/21.11  
% 20.93/21.11  % SZS output end Refutation
% 20.93/21.11  
% 20.93/21.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
