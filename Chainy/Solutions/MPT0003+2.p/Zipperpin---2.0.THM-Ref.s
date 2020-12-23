%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ia00KoH41V

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 157 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  715 (1417 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t3_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( ( r2_hidden @ ( C @ B ) )
                & ( r2_hidden @ ( C @ A ) ) )
            & ( r1_xboole_0 @ ( A @ B ) ) )
        & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
            & ! [C: $i] :
                ~ ( ( r2_hidden @ ( C @ A ) )
                  & ( r2_hidden @ ( C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_xboole_0])).

thf('0',plain,(
    ! [X48: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X48: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
    | ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X48: $i] :
      ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
   <= ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
   <= ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
      & ! [X48: $i] :
          ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
          | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
    | ~ ! [X48: $i] :
          ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
          | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ ( X31 @ X32 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ ( X31 @ X32 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X31 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      = o_0_0_xboole_0 )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
   <= ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
   <= ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ~ ( r2_hidden @ ( X17 @ X19 ) )
      | ( r2_hidden @ ( X17 @ X20 ) )
      | ( X20
       != ( k3_xboole_0 @ ( X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( X17 @ ( k3_xboole_0 @ ( X18 @ X19 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X19 ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C_1 @ X0 ) )
        | ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) ) ) ) )
   <= ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ ( sk_B_1 @ sk_A_2 ) ) ) )
   <= ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
      & ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( X5 @ X4 ) )
      = ( k3_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ( ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
      & ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_C_1 @ o_0_0_xboole_0 ) )
   <= ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      & ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) )
      & ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( X29 @ X30 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X29 @ X30 ) @ ( k4_xboole_0 @ ( X30 @ X29 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k2_xboole_0 @ ( X34 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( X0 @ X0 ) )
      = ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
    <=> ~ ( ( r2_hidden @ ( A @ B ) )
        <=> ( r2_hidden @ ( A @ C ) ) ) ) )).

thf('31',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ ( X39 @ X40 ) )
      | ~ ( r2_hidden @ ( X39 @ X41 ) )
      | ~ ( r2_hidden @ ( X39 @ ( k5_xboole_0 @ ( X40 @ X41 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ X0 ) )
      | ~ ( r2_hidden @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ~ ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( X27 @ X26 ) )
      | ( r2_hidden @ ( X27 @ X24 ) )
      | ( X26
       != ( k4_xboole_0 @ ( X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ ( X27 @ X24 ) )
      | ~ ( r2_hidden @ ( X27 @ ( k4_xboole_0 @ ( X24 @ X25 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','35'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','35'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    ! [X36: $i] :
      ( ( X36 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ ( X1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( X5 @ X4 ) )
      = ( k3_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( X21 @ X20 ) )
      | ( r2_hidden @ ( X21 @ X19 ) )
      | ( X20
       != ( k3_xboole_0 @ ( X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ ( X21 @ X19 ) )
      | ~ ( r2_hidden @ ( X21 @ ( k3_xboole_0 @ ( X18 @ X19 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ ( X1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ ( X21 @ X19 ) )
      | ~ ( r2_hidden @ ( X21 @ ( k3_xboole_0 @ ( X18 @ X19 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ ( X1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) ) )
        | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) ) @ sk_B_1 ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_B_1 @ sk_A_2 ) ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_B_1 @ sk_A_2 ) ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( X5 @ X4 ) )
      = ( k3_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( X5 @ X4 ) )
      = ( k3_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X36: $i] :
      ( ( X36 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      = o_0_0_xboole_0 )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( X31 @ X33 ) )
      | ( ( k3_xboole_0 @ ( X31 @ X33 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('67',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( X31 @ X33 ) )
      | ( ( k3_xboole_0 @ ( X31 @ X33 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ! [X48: $i] :
        ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
        | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('71',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ~ ! [X48: $i] :
          ( ~ ( r2_hidden @ ( X48 @ sk_A_2 ) )
          | ~ ( r2_hidden @ ( X48 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','12','13','45','46','71'])).

%------------------------------------------------------------------------------
