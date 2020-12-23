%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0050+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TJCD2i76MS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 31.47s
% Output     : Refutation 31.47s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 133 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  564 ( 893 expanded)
%              Number of equality atoms :   55 (  95 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t43_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
       => ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X199: $i,X200: $i] :
      ( r1_tarski @ ( X199 @ ( k2_xboole_0 @ ( X199 @ X200 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('9',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( r1_tarski @ ( X91 @ X92 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X91 @ X93 ) @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X188: $i,X189: $i,X190: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X188 @ X189 ) @ X190 ) )
      = ( k2_xboole_0 @ ( X188 @ ( k2_xboole_0 @ ( X189 @ X190 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('15',plain,(
    ! [X143: $i,X144: $i] :
      ( ( ( k3_xboole_0 @ ( X143 @ X144 ) )
        = X143 )
      | ~ ( r1_tarski @ ( X143 @ X144 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X108: $i,X109: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X108 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('19',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X181: $i,X182: $i,X183: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X181 @ X182 ) @ X183 ) )
      = ( k4_xboole_0 @ ( X181 @ ( k2_xboole_0 @ ( X182 @ X183 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X2 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X2 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ X0 ) @ sk_C_5 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('30',plain,(
    ! [X175: $i,X176: $i] :
      ( ( k2_xboole_0 @ ( X175 @ ( k4_xboole_0 @ ( X176 @ X175 ) ) ) )
      = ( k2_xboole_0 @ ( X175 @ X176 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('32',plain,(
    ! [X179: $i,X180: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X179 @ X180 ) @ X180 ) )
      = ( k4_xboole_0 @ ( X179 @ X180 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X199: $i,X200: $i] :
      ( r1_tarski @ ( X199 @ ( k2_xboole_0 @ ( X199 @ X200 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('41',plain,(
    ! [X149: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X149 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X149: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X149 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','39','40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','39','40','45'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['29','49'])).

thf('51',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
