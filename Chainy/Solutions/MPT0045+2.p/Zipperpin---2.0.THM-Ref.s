%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0045+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UaZD3kcsI5

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 306 expanded)
%              Number of leaves         :   33 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  662 (1926 expanded)
%              Number of equality atoms :   54 ( 164 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t38_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t38_xboole_1])).

thf('0',plain,(
    r1_tarski @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('3',plain,(
    ! [X123: $i,X124: $i] :
      ( ( k3_xboole_0 @ ( X123 @ ( k2_xboole_0 @ ( X123 @ X124 ) ) ) )
      = X123 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('6',plain,(
    ! [X125: $i,X126: $i] :
      ( ( k2_xboole_0 @ ( X125 @ ( k3_xboole_0 @ ( X125 @ X126 ) ) ) )
      = X125 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_A_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('11',plain,(
    ! [X168: $i,X169: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X168 @ X169 ) @ X168 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('13',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( r1_tarski @ ( X91 @ X92 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X91 @ X93 ) @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('16',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('21',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('23',plain,(
    ! [X116: $i] :
      ( ( k2_xboole_0 @ ( X116 @ k1_xboole_0 ) )
      = X116 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X116: $i] :
      ( ( k2_xboole_0 @ ( X116 @ o_0_0_xboole_0 ) )
      = X116 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
    = ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','27','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A_2 )
    | ( r2_hidden @ ( sk_B @ sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('35',plain,(
    ! [X189: $i,X190: $i] :
      ( ~ ( v1_xboole_0 @ X189 )
      | ~ ( v1_xboole_0 @ X190 )
      | ( X189 = X190 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('36',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('38',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference('simplify_reflect+',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ sk_A_2 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['34','42'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( X23 @ X24 ) )
      | ~ ( r2_hidden @ ( X23 @ X25 ) )
      | ( r2_hidden @ ( X23 @ X26 ) )
      | ( X26
       != ( k3_xboole_0 @ ( X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( X23 @ ( k3_xboole_0 @ ( X24 @ X25 ) ) ) )
      | ~ ( r2_hidden @ ( X23 @ X25 ) )
      | ~ ( r2_hidden @ ( X23 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ sk_A_2 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) @ sk_A_2 ) ) ) )
      | ( v1_xboole_0 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X187: $i,X188: $i] :
      ( r1_tarski @ ( X187 @ ( k2_xboole_0 @ ( X187 @ X188 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('55',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('56',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( r1_tarski @ ( X91 @ X92 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X91 @ X93 ) @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_B_2 @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('62',plain,(
    ! [X143: $i,X144: $i] :
      ( ( ( k3_xboole_0 @ ( X143 @ X144 ) )
        = X143 )
      | ~ ( r1_tarski @ ( X143 @ X144 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A_2 @ sk_A_2 ) )
    | ( v1_xboole_0 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['51','52','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference('simplify_reflect+',[status(thm)],['40','41'])).

thf('66',plain,(
    r2_hidden @ ( sk_B @ sk_A_2 @ sk_A_2 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X20 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('68',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_A_2 @ ( k2_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_B @ sk_A_2 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup+',[status(thm)],['29','69'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
    <=> ~ ( ( r2_hidden @ ( A @ B ) )
        <=> ( r2_hidden @ ( A @ C ) ) ) ) )).

thf('71',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ ( X49 @ X50 ) )
      | ~ ( r2_hidden @ ( X49 @ X51 ) )
      | ~ ( r2_hidden @ ( X49 @ ( k5_xboole_0 @ ( X50 @ X51 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_A_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( sk_B @ sk_A_2 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['34','42'])).

thf('74',plain,(
    r2_hidden @ ( sk_B @ sk_A_2 @ sk_A_2 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['72','73','74'])).

%------------------------------------------------------------------------------
