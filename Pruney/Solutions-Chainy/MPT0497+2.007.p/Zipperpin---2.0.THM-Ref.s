%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zuqYr0EjqO

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:06 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 197 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  865 (1735 expanded)
%              Number of equality atoms :   72 ( 155 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X51: $i] :
      ( ( ( k1_relat_1 @ X51 )
       != k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('32',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','27','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) ) @ X53 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('63',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['60','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['29','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zuqYr0EjqO
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:57:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 535 iterations in 0.268s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.70  thf(t95_relat_1, conjecture,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ B ) =>
% 0.52/0.70       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.70         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i,B:$i]:
% 0.52/0.70        ( ( v1_relat_1 @ B ) =>
% 0.52/0.70          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.70            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.52/0.70  thf('0', plain,
% 0.52/0.70      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.52/0.70        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.52/0.70         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('split', [status(esa)], ['0'])).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.52/0.70       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('split', [status(esa)], ['0'])).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.52/0.70        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('split', [status(esa)], ['3'])).
% 0.52/0.70  thf(t83_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X17 : $i, X18 : $i]:
% 0.52/0.70         (((k4_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_xboole_0 @ X17 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.70  thf(t48_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.52/0.70          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.70  thf(t3_boole, axiom,
% 0.52/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.70  thf('9', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.70  thf(t2_boole, axiom,
% 0.52/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.70  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('demod', [status(thm)], ['8', '13'])).
% 0.52/0.70  thf(dt_k7_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X49 : $i, X50 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.52/0.70  thf(t90_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ B ) =>
% 0.52/0.70       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.52/0.70         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      (![X54 : $i, X55 : $i]:
% 0.52/0.70         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.52/0.70            = (k3_xboole_0 @ (k1_relat_1 @ X54) @ X55))
% 0.52/0.70          | ~ (v1_relat_1 @ X54))),
% 0.52/0.70      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.52/0.70  thf(t64_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X51 : $i]:
% 0.52/0.70         (((k1_relat_1 @ X51) != (k1_xboole_0))
% 0.52/0.70          | ((X51) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X51))),
% 0.52/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.52/0.70          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X1)
% 0.52/0.70          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1)
% 0.52/0.70          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['15', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.52/0.70          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70         | ~ (v1_relat_1 @ sk_B)
% 0.52/0.70         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['14', '20'])).
% 0.52/0.70  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.52/0.70         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['0'])).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.70         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.52/0.70             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.70      inference('simplify', [status(thm)], ['26'])).
% 0.52/0.70  thf('28', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.52/0.70  thf('29', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.52/0.70         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['3'])).
% 0.52/0.70  thf('31', plain,
% 0.52/0.70      (![X54 : $i, X55 : $i]:
% 0.52/0.70         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.52/0.70            = (k3_xboole_0 @ (k1_relat_1 @ X54) @ X55))
% 0.52/0.70          | ~ (v1_relat_1 @ X54))),
% 0.52/0.70      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (((((k1_relat_1 @ k1_xboole_0)
% 0.52/0.70           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.52/0.70         | ~ (v1_relat_1 @ sk_B)))
% 0.52/0.70         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.70  thf(t60_relat_1, axiom,
% 0.52/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.70  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.70  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.52/0.70         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.52/0.70       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.70      inference('split', [status(esa)], ['3'])).
% 0.52/0.70  thf('37', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['2', '27', '36'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X15 : $i, X16 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.52/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.70           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X54 : $i, X55 : $i]:
% 0.52/0.70         (((k1_relat_1 @ (k7_relat_1 @ X54 @ X55))
% 0.52/0.70            = (k3_xboole_0 @ (k1_relat_1 @ X54) @ X55))
% 0.52/0.70          | ~ (v1_relat_1 @ X54))),
% 0.52/0.70      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.52/0.70  thf(t87_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ B ) =>
% 0.52/0.70       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X52 : $i, X53 : $i]:
% 0.52/0.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X52 @ X53)) @ X53)
% 0.52/0.70          | ~ (v1_relat_1 @ X52))),
% 0.52/0.70      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['42', '43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X1)
% 0.52/0.70          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r1_tarski @ 
% 0.52/0.70           (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.52/0.70            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ 
% 0.52/0.70           (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['41', '45'])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      (((r1_tarski @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0) @ 
% 0.52/0.70         (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.52/0.70        | ~ (v1_relat_1 @ sk_B))),
% 0.52/0.70      inference('sup+', [status(thm)], ['38', '46'])).
% 0.52/0.70  thf('48', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.70  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      ((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 0.52/0.70        (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.52/0.70  thf(d3_tarski, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.70  thf('51', plain,
% 0.52/0.70      (![X1 : $i, X3 : $i]:
% 0.52/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.70  thf(d5_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.70       ( ![D:$i]:
% 0.52/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.70           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.70          | (r2_hidden @ X8 @ X5)
% 0.52/0.70          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.52/0.70      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.70  thf('53', plain,
% 0.52/0.70      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.70         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['52'])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.70          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['51', '53'])).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      (![X1 : $i, X3 : $i]:
% 0.52/0.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.70  thf('56', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.70          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.70  thf('57', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.52/0.70      inference('simplify', [status(thm)], ['56'])).
% 0.52/0.70  thf(d10_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      (![X10 : $i, X12 : $i]:
% 0.52/0.70         (((X10) = (X12))
% 0.52/0.70          | ~ (r1_tarski @ X12 @ X10)
% 0.52/0.70          | ~ (r1_tarski @ X10 @ X12))),
% 0.52/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.70  thf('59', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.52/0.70          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.52/0.70  thf('60', plain,
% 0.52/0.70      (((k1_relat_1 @ sk_B) = (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['50', '59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X4 @ X5)
% 0.52/0.71          | (r2_hidden @ X4 @ X6)
% 0.52/0.71          | (r2_hidden @ X4 @ X7)
% 0.52/0.71          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.71         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.52/0.71          | (r2_hidden @ X4 @ X6)
% 0.52/0.71          | ~ (r2_hidden @ X4 @ X5))),
% 0.52/0.71      inference('simplify', [status(thm)], ['62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         ((r1_tarski @ X0 @ X1)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['61', '63'])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.52/0.71          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.71          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['64', '65'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.71          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['66'])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.71          | ~ (r2_hidden @ X8 @ X6)
% 0.52/0.71          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.52/0.71          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.71          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['68', '70'])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.52/0.71           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 0.52/0.71          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.52/0.71             (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['67', '71'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.52/0.71          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['72'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.52/0.71          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X1 @ X0)
% 0.52/0.71           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X17 : $i, X19 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 0.52/0.71          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['75', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.52/0.71      inference('simplify', [status(thm)], ['77'])).
% 0.52/0.71  thf('79', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.52/0.71      inference('sup+', [status(thm)], ['60', '78'])).
% 0.52/0.71  thf('80', plain, ($false), inference('demod', [status(thm)], ['29', '79'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
