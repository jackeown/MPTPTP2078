%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jn9TIBIWnI

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:02 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 102 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  666 ( 774 expanded)
%              Number of equality atoms :   56 (  67 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t39_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
        = ( k2_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t39_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( r1_tarski @ X40 @ ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ ( k4_xboole_0 @ X32 @ X31 ) @ ( k4_xboole_0 @ X32 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

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
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k3_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X29: $i] :
      ( ( k3_xboole_0 @ X29 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','33'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X33 @ X34 ) @ X33 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k2_xboole_0 @ X35 @ ( k2_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X40: $i,X41: $i] :
      ( r1_tarski @ X40 @ ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k2_xboole_0 @ X35 @ ( k2_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','58'])).

thf('60',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jn9TIBIWnI
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.95/2.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.95/2.18  % Solved by: fo/fo7.sh
% 1.95/2.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.18  % done 2992 iterations in 1.741s
% 1.95/2.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.95/2.18  % SZS output start Refutation
% 1.95/2.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.95/2.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.95/2.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.95/2.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.95/2.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.95/2.18  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.95/2.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.95/2.18  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.95/2.18  thf(t39_xboole_1, conjecture,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.95/2.18  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.18    (~( ![A:$i,B:$i]:
% 1.95/2.18        ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) =
% 1.95/2.18          ( k2_xboole_0 @ A @ B ) ) )),
% 1.95/2.18    inference('cnf.neg', [status(esa)], [t39_xboole_1])).
% 1.95/2.18  thf('0', plain,
% 1.95/2.18      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 1.95/2.18         != (k2_xboole_0 @ sk_A @ sk_B))),
% 1.95/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.18  thf(commutativity_k2_xboole_0, axiom,
% 1.95/2.18    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.95/2.18  thf('1', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf('2', plain,
% 1.95/2.18      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 1.95/2.18         != (k2_xboole_0 @ sk_B @ sk_A))),
% 1.95/2.18      inference('demod', [status(thm)], ['0', '1'])).
% 1.95/2.18  thf(t7_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.95/2.18  thf('3', plain,
% 1.95/2.18      (![X40 : $i, X41 : $i]: (r1_tarski @ X40 @ (k2_xboole_0 @ X40 @ X41))),
% 1.95/2.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.18  thf(t34_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i,C:$i]:
% 1.95/2.18     ( ( r1_tarski @ A @ B ) =>
% 1.95/2.18       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 1.95/2.18  thf('4', plain,
% 1.95/2.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.95/2.18         (~ (r1_tarski @ X30 @ X31)
% 1.95/2.18          | (r1_tarski @ (k4_xboole_0 @ X32 @ X31) @ (k4_xboole_0 @ X32 @ X30)))),
% 1.95/2.18      inference('cnf', [status(esa)], [t34_xboole_1])).
% 1.95/2.18  thf('5', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.95/2.18          (k4_xboole_0 @ X2 @ X1))),
% 1.95/2.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.95/2.18  thf(t28_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.95/2.18  thf('6', plain,
% 1.95/2.18      (![X27 : $i, X28 : $i]:
% 1.95/2.18         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 1.95/2.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.95/2.18  thf('7', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ 
% 1.95/2.18           (k4_xboole_0 @ X1 @ X0))
% 1.95/2.18           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.95/2.18      inference('sup-', [status(thm)], ['5', '6'])).
% 1.95/2.18  thf(commutativity_k3_xboole_0, axiom,
% 1.95/2.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.95/2.18  thf('8', plain,
% 1.95/2.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.95/2.18  thf('9', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.95/2.18           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 1.95/2.18           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.95/2.18      inference('demod', [status(thm)], ['7', '8'])).
% 1.95/2.18  thf('10', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf(t21_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.95/2.18  thf('11', plain,
% 1.95/2.18      (![X25 : $i, X26 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (X25))),
% 1.95/2.18      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.95/2.18  thf('12', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.95/2.18      inference('sup+', [status(thm)], ['10', '11'])).
% 1.95/2.18  thf(t3_xboole_0, axiom,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.95/2.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.95/2.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.95/2.18            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.95/2.18  thf('13', plain,
% 1.95/2.18      (![X13 : $i, X14 : $i]:
% 1.95/2.18         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 1.95/2.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.18  thf('14', plain,
% 1.95/2.18      (![X13 : $i, X14 : $i]:
% 1.95/2.18         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 1.95/2.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.18  thf(d5_xboole_0, axiom,
% 1.95/2.18    (![A:$i,B:$i,C:$i]:
% 1.95/2.18     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.95/2.18       ( ![D:$i]:
% 1.95/2.18         ( ( r2_hidden @ D @ C ) <=>
% 1.95/2.18           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.95/2.18  thf('15', plain,
% 1.95/2.18      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.95/2.18         (~ (r2_hidden @ X8 @ X7)
% 1.95/2.18          | ~ (r2_hidden @ X8 @ X6)
% 1.95/2.18          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.95/2.18      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.95/2.18  thf('16', plain,
% 1.95/2.18      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.95/2.18         (~ (r2_hidden @ X8 @ X6)
% 1.95/2.18          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.95/2.18      inference('simplify', [status(thm)], ['15'])).
% 1.95/2.18  thf('17', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.95/2.18          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['14', '16'])).
% 1.95/2.18  thf('18', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.95/2.18          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['13', '17'])).
% 1.95/2.18  thf('19', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.95/2.18      inference('simplify', [status(thm)], ['18'])).
% 1.95/2.18  thf(d7_xboole_0, axiom,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.95/2.18       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.95/2.18  thf('20', plain,
% 1.95/2.18      (![X10 : $i, X11 : $i]:
% 1.95/2.18         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 1.95/2.18          | ~ (r1_xboole_0 @ X10 @ X11))),
% 1.95/2.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.95/2.18  thf('21', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['19', '20'])).
% 1.95/2.18  thf('22', plain,
% 1.95/2.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.95/2.18  thf('23', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.95/2.18      inference('demod', [status(thm)], ['21', '22'])).
% 1.95/2.18  thf(t16_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i,C:$i]:
% 1.95/2.18     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.95/2.18       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.95/2.18  thf('24', plain,
% 1.95/2.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24)
% 1.95/2.18           = (k3_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24)))),
% 1.95/2.18      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.95/2.18  thf('25', plain,
% 1.95/2.18      (![X10 : $i, X12 : $i]:
% 1.95/2.18         ((r1_xboole_0 @ X10 @ X12)
% 1.95/2.18          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 1.95/2.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.95/2.18  thf('26', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.95/2.18          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['24', '25'])).
% 1.95/2.18  thf('27', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (((k3_xboole_0 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 1.95/2.18          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('sup-', [status(thm)], ['23', '26'])).
% 1.95/2.18  thf(t2_boole, axiom,
% 1.95/2.18    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.95/2.18  thf('28', plain,
% 1.95/2.18      (![X29 : $i]: ((k3_xboole_0 @ X29 @ k1_xboole_0) = (k1_xboole_0))),
% 1.95/2.18      inference('cnf', [status(esa)], [t2_boole])).
% 1.95/2.18  thf('29', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (((k1_xboole_0) != (k1_xboole_0))
% 1.95/2.18          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('demod', [status(thm)], ['27', '28'])).
% 1.95/2.18  thf('30', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 1.95/2.18      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.18  thf('31', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('sup+', [status(thm)], ['12', '30'])).
% 1.95/2.18  thf('32', plain,
% 1.95/2.18      (![X10 : $i, X11 : $i]:
% 1.95/2.18         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 1.95/2.18          | ~ (r1_xboole_0 @ X10 @ X11))),
% 1.95/2.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.95/2.18  thf('33', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.95/2.18           = (k1_xboole_0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.95/2.18  thf('34', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.95/2.18           = (k1_xboole_0))),
% 1.95/2.18      inference('sup+', [status(thm)], ['9', '33'])).
% 1.95/2.18  thf(l32_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.95/2.18  thf('35', plain,
% 1.95/2.18      (![X17 : $i, X18 : $i]:
% 1.95/2.18         ((r1_tarski @ X17 @ X18)
% 1.95/2.18          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 1.95/2.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.95/2.18  thf('36', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         (((k1_xboole_0) != (k1_xboole_0))
% 1.95/2.18          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.95/2.18      inference('sup-', [status(thm)], ['34', '35'])).
% 1.95/2.18  thf('37', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('simplify', [status(thm)], ['36'])).
% 1.95/2.18  thf(t12_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]:
% 1.95/2.18     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.95/2.18  thf('38', plain,
% 1.95/2.18      (![X20 : $i, X21 : $i]:
% 1.95/2.18         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 1.95/2.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.18  thf('39', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.95/2.18           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('sup-', [status(thm)], ['37', '38'])).
% 1.95/2.18  thf('40', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf(t36_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.95/2.18  thf('41', plain,
% 1.95/2.18      (![X33 : $i, X34 : $i]: (r1_tarski @ (k4_xboole_0 @ X33 @ X34) @ X33)),
% 1.95/2.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.95/2.18  thf('42', plain,
% 1.95/2.18      (![X20 : $i, X21 : $i]:
% 1.95/2.18         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 1.95/2.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.18  thf('43', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['41', '42'])).
% 1.95/2.18  thf('44', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf('45', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.95/2.18      inference('demod', [status(thm)], ['43', '44'])).
% 1.95/2.18  thf(t4_xboole_1, axiom,
% 1.95/2.18    (![A:$i,B:$i,C:$i]:
% 1.95/2.18     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.95/2.18       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.95/2.18  thf('46', plain,
% 1.95/2.18      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ (k2_xboole_0 @ X35 @ X36) @ X37)
% 1.95/2.18           = (k2_xboole_0 @ X35 @ (k2_xboole_0 @ X36 @ X37)))),
% 1.95/2.18      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.95/2.18  thf('47', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf('48', plain,
% 1.95/2.18      (![X40 : $i, X41 : $i]: (r1_tarski @ X40 @ (k2_xboole_0 @ X40 @ X41))),
% 1.95/2.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.18  thf('49', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.95/2.18      inference('sup+', [status(thm)], ['47', '48'])).
% 1.95/2.18  thf('50', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('sup+', [status(thm)], ['46', '49'])).
% 1.95/2.18  thf('51', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 1.95/2.18      inference('sup+', [status(thm)], ['45', '50'])).
% 1.95/2.18  thf('52', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 1.95/2.18      inference('sup+', [status(thm)], ['40', '51'])).
% 1.95/2.18  thf('53', plain,
% 1.95/2.18      (![X20 : $i, X21 : $i]:
% 1.95/2.18         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 1.95/2.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.18  thf('54', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 1.95/2.18           = (k2_xboole_0 @ X1 @ X0))),
% 1.95/2.18      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.18  thf('55', plain,
% 1.95/2.18      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ (k2_xboole_0 @ X35 @ X36) @ X37)
% 1.95/2.18           = (k2_xboole_0 @ X35 @ (k2_xboole_0 @ X36 @ X37)))),
% 1.95/2.18      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.95/2.18  thf('56', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.95/2.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.95/2.18  thf('57', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 1.95/2.18           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('sup+', [status(thm)], ['55', '56'])).
% 1.95/2.18  thf('58', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2)))
% 1.95/2.18           = (k2_xboole_0 @ X1 @ X0))),
% 1.95/2.18      inference('demod', [status(thm)], ['54', '57'])).
% 1.95/2.18  thf('59', plain,
% 1.95/2.18      (![X0 : $i, X1 : $i]:
% 1.95/2.18         ((k2_xboole_0 @ X1 @ X0)
% 1.95/2.18           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.18      inference('demod', [status(thm)], ['39', '58'])).
% 1.95/2.18  thf('60', plain,
% 1.95/2.18      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 1.95/2.18      inference('demod', [status(thm)], ['2', '59'])).
% 1.95/2.18  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 1.95/2.18  
% 1.95/2.18  % SZS output end Refutation
% 1.95/2.18  
% 1.95/2.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
