%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3sINhxujCo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 29.82s
% Output     : Refutation 29.82s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 215 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          :  640 (1597 expanded)
%              Number of equality atoms :   64 ( 156 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ ( k4_xboole_0 @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ ( k4_xboole_0 @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X38: $i] :
      ( r1_xboole_0 @ X38 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ ( k4_xboole_0 @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['28','35'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ X0 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ ( k4_xboole_0 @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_1 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X39: $i,X40: $i] :
      ( r1_tarski @ X39 @ ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3sINhxujCo
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.82/30.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.82/30.02  % Solved by: fo/fo7.sh
% 29.82/30.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.82/30.02  % done 23238 iterations in 29.561s
% 29.82/30.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.82/30.02  % SZS output start Refutation
% 29.82/30.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.82/30.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 29.82/30.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 29.82/30.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.82/30.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 29.82/30.02  thf(sk_A_type, type, sk_A: $i).
% 29.82/30.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.82/30.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.82/30.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.82/30.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.82/30.02  thf(sk_B_type, type, sk_B: $i > $i).
% 29.82/30.02  thf(t73_xboole_1, conjecture,
% 29.82/30.02    (![A:$i,B:$i,C:$i]:
% 29.82/30.02     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 29.82/30.02       ( r1_tarski @ A @ B ) ))).
% 29.82/30.02  thf(zf_stmt_0, negated_conjecture,
% 29.82/30.02    (~( ![A:$i,B:$i,C:$i]:
% 29.82/30.02        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 29.82/30.02            ( r1_xboole_0 @ A @ C ) ) =>
% 29.82/30.02          ( r1_tarski @ A @ B ) ) )),
% 29.82/30.02    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 29.82/30.02  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 29.82/30.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.82/30.02  thf(t7_xboole_0, axiom,
% 29.82/30.02    (![A:$i]:
% 29.82/30.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 29.82/30.02          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 29.82/30.02  thf('1', plain,
% 29.82/30.02      (![X28 : $i]:
% 29.82/30.02         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 29.82/30.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 29.82/30.02  thf(d5_xboole_0, axiom,
% 29.82/30.02    (![A:$i,B:$i,C:$i]:
% 29.82/30.02     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 29.82/30.02       ( ![D:$i]:
% 29.82/30.02         ( ( r2_hidden @ D @ C ) <=>
% 29.82/30.02           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 29.82/30.02  thf('2', plain,
% 29.82/30.02      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 29.82/30.02         (~ (r2_hidden @ X12 @ X11)
% 29.82/30.02          | (r2_hidden @ X12 @ X9)
% 29.82/30.02          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 29.82/30.02      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.82/30.02  thf('3', plain,
% 29.82/30.02      (![X9 : $i, X10 : $i, X12 : $i]:
% 29.82/30.02         ((r2_hidden @ X12 @ X9)
% 29.82/30.02          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 29.82/30.02      inference('simplify', [status(thm)], ['2'])).
% 29.82/30.02  thf('4', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 29.82/30.02          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 29.82/30.02      inference('sup-', [status(thm)], ['1', '3'])).
% 29.82/30.02  thf('5', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 29.82/30.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.82/30.02  thf(d3_tarski, axiom,
% 29.82/30.02    (![A:$i,B:$i]:
% 29.82/30.02     ( ( r1_tarski @ A @ B ) <=>
% 29.82/30.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 29.82/30.02  thf('6', plain,
% 29.82/30.02      (![X4 : $i, X5 : $i, X6 : $i]:
% 29.82/30.02         (~ (r2_hidden @ X4 @ X5)
% 29.82/30.02          | (r2_hidden @ X4 @ X6)
% 29.82/30.02          | ~ (r1_tarski @ X5 @ X6))),
% 29.82/30.02      inference('cnf', [status(esa)], [d3_tarski])).
% 29.82/30.02  thf('7', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 29.82/30.02          | ~ (r2_hidden @ X0 @ sk_A))),
% 29.82/30.02      inference('sup-', [status(thm)], ['5', '6'])).
% 29.82/30.02  thf('8', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 29.82/30.02          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ sk_A @ X0)) @ 
% 29.82/30.02             (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 29.82/30.02      inference('sup-', [status(thm)], ['4', '7'])).
% 29.82/30.02  thf('9', plain,
% 29.82/30.02      (![X28 : $i]:
% 29.82/30.02         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 29.82/30.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 29.82/30.02  thf('10', plain,
% 29.82/30.02      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 29.82/30.02         (~ (r2_hidden @ X12 @ X11)
% 29.82/30.02          | ~ (r2_hidden @ X12 @ X10)
% 29.82/30.02          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 29.82/30.02      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.82/30.02  thf('11', plain,
% 29.82/30.02      (![X9 : $i, X10 : $i, X12 : $i]:
% 29.82/30.02         (~ (r2_hidden @ X12 @ X10)
% 29.82/30.02          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 29.82/30.02      inference('simplify', [status(thm)], ['10'])).
% 29.82/30.02  thf('12', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 29.82/30.02          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 29.82/30.02      inference('sup-', [status(thm)], ['9', '11'])).
% 29.82/30.02  thf('13', plain,
% 29.82/30.02      ((((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))
% 29.82/30.02        | ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 29.82/30.02            = (k1_xboole_0)))),
% 29.82/30.02      inference('sup-', [status(thm)], ['8', '12'])).
% 29.82/30.02  thf(t48_xboole_1, axiom,
% 29.82/30.02    (![A:$i,B:$i]:
% 29.82/30.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 29.82/30.02  thf('14', plain,
% 29.82/30.02      (![X34 : $i, X35 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ X34 @ (k4_xboole_0 @ X34 @ X35))
% 29.82/30.02           = (k3_xboole_0 @ X34 @ X35))),
% 29.82/30.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.82/30.02  thf(t39_xboole_1, axiom,
% 29.82/30.02    (![A:$i,B:$i]:
% 29.82/30.02     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 29.82/30.02  thf('15', plain,
% 29.82/30.02      (![X29 : $i, X30 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 29.82/30.02           = (k2_xboole_0 @ X29 @ X30))),
% 29.82/30.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 29.82/30.02  thf('16', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 29.82/30.02           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 29.82/30.02      inference('sup+', [status(thm)], ['14', '15'])).
% 29.82/30.02  thf(commutativity_k2_xboole_0, axiom,
% 29.82/30.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 29.82/30.02  thf('17', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.82/30.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.82/30.02  thf('18', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.82/30.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.82/30.02  thf('19', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 29.82/30.02           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 29.82/30.02      inference('demod', [status(thm)], ['16', '17', '18'])).
% 29.82/30.02  thf(t51_xboole_1, axiom,
% 29.82/30.02    (![A:$i,B:$i]:
% 29.82/30.02     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 29.82/30.02       ( A ) ))).
% 29.82/30.02  thf('20', plain,
% 29.82/30.02      (![X36 : $i, X37 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ (k4_xboole_0 @ X36 @ X37))
% 29.82/30.02           = (X36))),
% 29.82/30.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.82/30.02  thf('21', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 29.82/30.02      inference('sup+', [status(thm)], ['19', '20'])).
% 29.82/30.02  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 29.82/30.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.82/30.02  thf(symmetry_r1_xboole_0, axiom,
% 29.82/30.02    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 29.82/30.02  thf('23', plain,
% 29.82/30.02      (![X17 : $i, X18 : $i]:
% 29.82/30.02         ((r1_xboole_0 @ X17 @ X18) | ~ (r1_xboole_0 @ X18 @ X17))),
% 29.82/30.02      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 29.82/30.02  thf('24', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 29.82/30.02      inference('sup-', [status(thm)], ['22', '23'])).
% 29.82/30.02  thf(d7_xboole_0, axiom,
% 29.82/30.02    (![A:$i,B:$i]:
% 29.82/30.02     ( ( r1_xboole_0 @ A @ B ) <=>
% 29.82/30.02       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 29.82/30.02  thf('25', plain,
% 29.82/30.02      (![X14 : $i, X15 : $i]:
% 29.82/30.02         (((k3_xboole_0 @ X14 @ X15) = (k1_xboole_0))
% 29.82/30.02          | ~ (r1_xboole_0 @ X14 @ X15))),
% 29.82/30.02      inference('cnf', [status(esa)], [d7_xboole_0])).
% 29.82/30.02  thf('26', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 29.82/30.02      inference('sup-', [status(thm)], ['24', '25'])).
% 29.82/30.02  thf('27', plain,
% 29.82/30.02      (![X36 : $i, X37 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ (k4_xboole_0 @ X36 @ X37))
% 29.82/30.02           = (X36))),
% 29.82/30.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.82/30.02  thf('28', plain,
% 29.82/30.02      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 29.82/30.02      inference('sup+', [status(thm)], ['26', '27'])).
% 29.82/30.02  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 29.82/30.02  thf('29', plain, (![X38 : $i]: (r1_xboole_0 @ X38 @ k1_xboole_0)),
% 29.82/30.02      inference('cnf', [status(esa)], [t65_xboole_1])).
% 29.82/30.02  thf('30', plain,
% 29.82/30.02      (![X14 : $i, X15 : $i]:
% 29.82/30.02         (((k3_xboole_0 @ X14 @ X15) = (k1_xboole_0))
% 29.82/30.02          | ~ (r1_xboole_0 @ X14 @ X15))),
% 29.82/30.02      inference('cnf', [status(esa)], [d7_xboole_0])).
% 29.82/30.02  thf('31', plain,
% 29.82/30.02      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 29.82/30.02      inference('sup-', [status(thm)], ['29', '30'])).
% 29.82/30.02  thf('32', plain,
% 29.82/30.02      (![X36 : $i, X37 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ (k4_xboole_0 @ X36 @ X37))
% 29.82/30.02           = (X36))),
% 29.82/30.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.82/30.02  thf('33', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 29.82/30.02      inference('sup+', [status(thm)], ['31', '32'])).
% 29.82/30.02  thf('34', plain,
% 29.82/30.02      (![X29 : $i, X30 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 29.82/30.02           = (k2_xboole_0 @ X29 @ X30))),
% 29.82/30.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 29.82/30.02  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.82/30.02      inference('demod', [status(thm)], ['33', '34'])).
% 29.82/30.02  thf('36', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 29.82/30.02      inference('demod', [status(thm)], ['28', '35'])).
% 29.82/30.02  thf(t41_xboole_1, axiom,
% 29.82/30.02    (![A:$i,B:$i,C:$i]:
% 29.82/30.02     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 29.82/30.02       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 29.82/30.02  thf('37', plain,
% 29.82/30.02      (![X31 : $i, X32 : $i, X33 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 29.82/30.02           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 29.82/30.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 29.82/30.02  thf('38', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ sk_C_1 @ X0)
% 29.82/30.02           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 29.82/30.02      inference('sup+', [status(thm)], ['36', '37'])).
% 29.82/30.02  thf('39', plain,
% 29.82/30.02      (![X34 : $i, X35 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ X34 @ (k4_xboole_0 @ X34 @ X35))
% 29.82/30.02           = (k3_xboole_0 @ X34 @ X35))),
% 29.82/30.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.82/30.02  thf('40', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ X0))
% 29.82/30.02           = (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 29.82/30.02      inference('sup+', [status(thm)], ['38', '39'])).
% 29.82/30.02  thf('41', plain,
% 29.82/30.02      (![X34 : $i, X35 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ X34 @ (k4_xboole_0 @ X34 @ X35))
% 29.82/30.02           = (k3_xboole_0 @ X34 @ X35))),
% 29.82/30.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.82/30.02  thf('42', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k3_xboole_0 @ sk_C_1 @ X0)
% 29.82/30.02           = (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 29.82/30.02      inference('demod', [status(thm)], ['40', '41'])).
% 29.82/30.02  thf('43', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ X0))
% 29.82/30.02           = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 29.82/30.02      inference('sup+', [status(thm)], ['21', '42'])).
% 29.82/30.02  thf('44', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 29.82/30.02      inference('sup-', [status(thm)], ['24', '25'])).
% 29.82/30.02  thf('45', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 29.82/30.02      inference('demod', [status(thm)], ['43', '44'])).
% 29.82/30.02  thf(commutativity_k3_xboole_0, axiom,
% 29.82/30.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 29.82/30.02  thf('46', plain,
% 29.82/30.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.82/30.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.82/30.02  thf('47', plain,
% 29.82/30.02      (![X36 : $i, X37 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ (k4_xboole_0 @ X36 @ X37))
% 29.82/30.02           = (X36))),
% 29.82/30.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.82/30.02  thf('48', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 29.82/30.02           = (X0))),
% 29.82/30.02      inference('sup+', [status(thm)], ['46', '47'])).
% 29.82/30.02  thf('49', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ k1_xboole_0 @ 
% 29.82/30.02           (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_1))
% 29.82/30.02           = (k4_xboole_0 @ sk_A @ X0))),
% 29.82/30.02      inference('sup+', [status(thm)], ['45', '48'])).
% 29.82/30.02  thf('50', plain,
% 29.82/30.02      (![X31 : $i, X32 : $i, X33 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 29.82/30.02           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 29.82/30.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 29.82/30.02  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.82/30.02      inference('demod', [status(thm)], ['33', '34'])).
% 29.82/30.02  thf('52', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 29.82/30.02           = (k4_xboole_0 @ sk_A @ X0))),
% 29.82/30.02      inference('demod', [status(thm)], ['49', '50', '51'])).
% 29.82/30.02  thf('53', plain,
% 29.82/30.02      (![X0 : $i]:
% 29.82/30.02         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 29.82/30.02           = (k4_xboole_0 @ sk_A @ X0))),
% 29.82/30.02      inference('demod', [status(thm)], ['49', '50', '51'])).
% 29.82/30.02  thf('54', plain,
% 29.82/30.02      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 29.82/30.02        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 29.82/30.02      inference('demod', [status(thm)], ['13', '52', '53'])).
% 29.82/30.02  thf('55', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 29.82/30.02      inference('simplify', [status(thm)], ['54'])).
% 29.82/30.02  thf('56', plain,
% 29.82/30.02      (![X29 : $i, X30 : $i]:
% 29.82/30.02         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 29.82/30.02           = (k2_xboole_0 @ X29 @ X30))),
% 29.82/30.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 29.82/30.02  thf('57', plain,
% 29.82/30.02      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 29.82/30.02      inference('sup+', [status(thm)], ['55', '56'])).
% 29.82/30.02  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.82/30.02      inference('demod', [status(thm)], ['33', '34'])).
% 29.82/30.02  thf('59', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.82/30.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.82/30.02  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 29.82/30.02      inference('sup+', [status(thm)], ['58', '59'])).
% 29.82/30.02  thf('61', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 29.82/30.02      inference('demod', [status(thm)], ['57', '60'])).
% 29.82/30.02  thf('62', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.82/30.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.82/30.02  thf(t7_xboole_1, axiom,
% 29.82/30.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 29.82/30.02  thf('63', plain,
% 29.82/30.02      (![X39 : $i, X40 : $i]: (r1_tarski @ X39 @ (k2_xboole_0 @ X39 @ X40))),
% 29.82/30.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.82/30.02  thf('64', plain,
% 29.82/30.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 29.82/30.02      inference('sup+', [status(thm)], ['62', '63'])).
% 29.82/30.02  thf('65', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 29.82/30.02      inference('sup+', [status(thm)], ['61', '64'])).
% 29.82/30.02  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 29.82/30.02  
% 29.82/30.02  % SZS output end Refutation
% 29.82/30.02  
% 29.82/30.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
