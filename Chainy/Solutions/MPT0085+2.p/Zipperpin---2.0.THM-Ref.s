%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4R5kIA5JPW

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  426 ( 841 expanded)
%              Number of equality atoms :   48 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
        = ( k3_xboole_0 @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ ( A @ B ) )
       => ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          = ( k3_xboole_0 @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X185 @ X186 ) @ X186 ) )
      = ( k4_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ B ) ) ) )).

thf('9',plain,(
    ! [X283: $i,X284: $i,X285: $i] :
      ( ~ ( r1_xboole_0 @ ( X283 @ X284 ) )
      | ( r1_xboole_0 @ ( X283 @ ( k3_xboole_0 @ ( X284 @ X285 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_B_2 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('17',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( sk_B_2
      = ( k4_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('21',plain,(
    ! [X205: $i,X206: $i] :
      ( ( k4_xboole_0 @ ( X205 @ ( k4_xboole_0 @ ( X205 @ X206 ) ) ) )
      = ( k3_xboole_0 @ ( X205 @ X206 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('22',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('28',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_B_2 ) ) ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
 != ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['2','39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
