%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0079+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.prHHU1w2ZQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 22.89s
% Output     : Refutation 22.89s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 480 expanded)
%              Number of leaves         :   38 ( 165 expanded)
%              Depth                    :   21
%              Number of atoms          : 1174 (3382 expanded)
%              Number of equality atoms :  150 ( 457 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_6_type,type,(
    sk_D_6: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ ( A @ B ) )
          = ( k2_xboole_0 @ ( C @ D ) ) )
        & ( r1_xboole_0 @ ( C @ A ) )
        & ( r1_xboole_0 @ ( D @ B ) ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ ( A @ B ) )
            = ( k2_xboole_0 @ ( C @ D ) ) )
          & ( r1_xboole_0 @ ( C @ A ) )
          & ( r1_xboole_0 @ ( D @ B ) ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('4',plain,(
    ! [X129: $i,X130: $i] :
      ( ( k3_xboole_0 @ ( X129 @ ( k2_xboole_0 @ ( X129 @ X130 ) ) ) )
      = X129 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( sk_D_6 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = sk_D_6 ),
    inference('sup+',[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('8',plain,(
    ! [X131: $i,X132: $i] :
      ( ( k2_xboole_0 @ ( X131 @ ( k3_xboole_0 @ ( X131 @ X132 ) ) ) )
      = X131 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( sk_D_6 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X201: $i,X202: $i] :
      ( ( k4_xboole_0 @ ( X201 @ ( k2_xboole_0 @ ( X201 @ X202 ) ) ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X201: $i,X202: $i] :
      ( ( k4_xboole_0 @ ( X201 @ ( k2_xboole_0 @ ( X201 @ X202 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( sk_D_6 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X187: $i,X188: $i,X189: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X187 @ X188 ) @ X189 ) )
      = ( k4_xboole_0 @ ( X187 @ ( k2_xboole_0 @ ( X188 @ X189 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_D_6 @ sk_B_2 ) @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('19',plain,(
    ! [X181: $i,X182: $i] :
      ( ( k2_xboole_0 @ ( X181 @ ( k4_xboole_0 @ ( X182 @ X181 ) ) ) )
      = ( k2_xboole_0 @ ( X181 @ X182 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_D_6 @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

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
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ k1_xboole_0 ) )
      = X122 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ o_0_0_xboole_0 ) )
      = X122 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( sk_A_2
    = ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_D_6 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( sk_D_6 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('29',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('35',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( sk_B_2 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('37',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B_2
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('42',plain,
    ( ( k5_xboole_0 @ ( sk_B_2 @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_D_6 @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X181: $i,X182: $i] :
      ( ( k2_xboole_0 @ ( X181 @ ( k4_xboole_0 @ ( X182 @ X181 ) ) ) )
      = ( k2_xboole_0 @ ( X181 @ X182 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,
    ( ( k5_xboole_0 @ ( sk_B_2 @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('45',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X185 @ X186 ) @ X186 ) )
      = ( k4_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_D_6 ) @ sk_D_6 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B_2
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_D_6 ) @ sk_D_6 ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['46','47'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('49',plain,(
    ! [X205: $i,X206: $i] :
      ( ( k4_xboole_0 @ ( X205 @ ( k4_xboole_0 @ ( X205 @ X206 ) ) ) )
      = ( k3_xboole_0 @ ( X205 @ X206 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('50',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('51',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('56',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_D_6
    = ( k4_xboole_0 @ ( sk_D_6 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf('63',plain,
    ( sk_A_2
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['27','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( sk_D_6 @ sk_A_2 ) )
    = sk_D_6 ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_D_6 ) )
    = sk_D_6 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('70',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('74',plain,
    ( sk_C_5
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('75',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( k4_xboole_0 @ ( X88 @ ( k3_xboole_0 @ ( X89 @ X90 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X88 @ X89 ) @ ( k4_xboole_0 @ ( X88 @ X90 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( sk_C_5 @ ( k4_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('78',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = sk_C_5 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = sk_C_5 ),
    inference('sup+',[status(thm)],['67','82'])).

thf('84',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('85',plain,
    ( ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ ( k4_xboole_0 @ ( sk_D_6 @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X181: $i,X182: $i] :
      ( ( k2_xboole_0 @ ( X181 @ ( k4_xboole_0 @ ( X182 @ X181 ) ) ) )
      = ( k2_xboole_0 @ ( X181 @ X182 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('87',plain,
    ( ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('89',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X129: $i,X130: $i] :
      ( ( k3_xboole_0 @ ( X129 @ ( k2_xboole_0 @ ( X129 @ X130 ) ) ) )
      = X129 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('91',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ) )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('93',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('94',plain,(
    ! [X133: $i,X134: $i,X135: $i] :
      ( ( k3_xboole_0 @ ( X133 @ ( k2_xboole_0 @ ( X134 @ X135 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( X133 @ X134 ) @ ( k3_xboole_0 @ ( X133 @ X135 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( X0 @ sk_D_6 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( X0 @ sk_D_6 ) ) ) )
      = ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ) )
    = ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup+',[status(thm)],['92','98'])).

thf('100',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('101',plain,(
    ! [X278: $i,X279: $i] :
      ( r1_tarski @ ( X278 @ ( k2_xboole_0 @ ( X278 @ X279 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('102',plain,(
    r1_tarski @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X187: $i,X188: $i,X189: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X187 @ X188 ) @ X189 ) )
      = ( k4_xboole_0 @ ( X187 @ ( k2_xboole_0 @ ( X188 @ X189 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('106',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('108',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('109',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['110'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('112',plain,(
    ! [X149: $i,X150: $i] :
      ( ( ( k3_xboole_0 @ ( X149 @ X150 ) )
        = X149 )
      | ~ ( r1_tarski @ ( X149 @ X150 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('113',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) )
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = sk_C_5 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('115',plain,(
    ! [X214: $i,X215: $i,X216: $i] :
      ( ( k3_xboole_0 @ ( X214 @ ( k4_xboole_0 @ ( X215 @ X216 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X214 @ X215 ) @ ( k3_xboole_0 @ ( X214 @ X216 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('116',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('117',plain,(
    ! [X214: $i,X215: $i,X216: $i] :
      ( ( k3_xboole_0 @ ( X214 @ ( k4_xboole_0 @ ( X215 @ X216 ) ) ) )
      = ( k3_xboole_0 @ ( X214 @ ( k4_xboole_0 @ ( X215 @ ( k3_xboole_0 @ ( X214 @ X216 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_C_5 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_C_5 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_A_2 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( o_0_0_xboole_0
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['113','123'])).

thf('125',plain,(
    ! [X205: $i,X206: $i] :
      ( ( k4_xboole_0 @ ( X205 @ ( k4_xboole_0 @ ( X205 @ X206 ) ) ) )
      = ( k3_xboole_0 @ ( X205 @ X206 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('126',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ o_0_0_xboole_0 ) )
    = ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('128',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('129',plain,
    ( sk_C_5
    = ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ ( k5_xboole_0 @ ( sk_C_5 @ sk_D_6 ) ) ) )
    = sk_C_5 ),
    inference(demod,[status(thm)],['99','129'])).

thf('131',plain,(
    sk_B_2 = sk_C_5 ),
    inference('sup+',[status(thm)],['91','130'])).

thf('132',plain,(
    sk_C_5 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
