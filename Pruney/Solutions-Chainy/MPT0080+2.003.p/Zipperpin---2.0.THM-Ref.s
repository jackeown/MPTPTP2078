%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gki6FZiP0u

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 506 expanded)
%              Number of leaves         :   24 ( 177 expanded)
%              Depth                    :   25
%              Number of atoms          : 1126 (3649 expanded)
%              Number of equality atoms :  116 ( 416 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,
    ( sk_C_2
    = ( k3_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('81',plain,(
    r1_tarski @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) )
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('85',plain,
    ( sk_C_2
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_2 @ X0 )
      = ( k4_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','87'])).

thf('89',plain,
    ( sk_C_2
    = ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('92',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('99',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','104','105'])).

thf('107',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['90','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['55','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['54','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','120'])).

thf('122',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','121'])).

thf('123',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('124',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('128',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('130',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('132',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gki6FZiP0u
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.09  % Solved by: fo/fo7.sh
% 0.91/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.09  % done 1597 iterations in 0.632s
% 0.91/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.09  % SZS output start Refutation
% 0.91/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.91/1.09  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.91/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.09  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.09  thf(t73_xboole_1, conjecture,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.91/1.09       ( r1_tarski @ A @ B ) ))).
% 0.91/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.09        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.91/1.09            ( r1_xboole_0 @ A @ C ) ) =>
% 0.91/1.09          ( r1_tarski @ A @ B ) ) )),
% 0.91/1.09    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.91/1.09  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t3_boole, axiom,
% 0.91/1.09    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.09  thf('1', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf(t48_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('2', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('3', plain,
% 0.91/1.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['1', '2'])).
% 0.91/1.09  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.91/1.09  thf('4', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 0.91/1.09      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.91/1.09  thf(d7_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.91/1.09       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.09  thf('5', plain,
% 0.91/1.09      (![X8 : $i, X9 : $i]:
% 0.91/1.09         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.09  thf('6', plain,
% 0.91/1.09      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.09  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['3', '6'])).
% 0.91/1.09  thf('8', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('9', plain,
% 0.91/1.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['7', '8'])).
% 0.91/1.09  thf('10', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf('11', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.09  thf(t4_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.09            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.09       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.09            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.09  thf('12', plain,
% 0.91/1.09      (![X11 : $i, X12 : $i]:
% 0.91/1.09         ((r1_xboole_0 @ X11 @ X12)
% 0.91/1.09          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.09  thf('13', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((r2_hidden @ (sk_C_1 @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.09  thf('14', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t12_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.09  thf('15', plain,
% 0.91/1.09      (![X15 : $i, X16 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('16', plain,
% 0.91/1.09      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.91/1.09         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.91/1.09      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.09  thf(t40_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('17', plain,
% 0.91/1.09      (![X20 : $i, X21 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.91/1.09           = (k4_xboole_0 @ X20 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.09  thf('18', plain,
% 0.91/1.09      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 0.91/1.09         (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.91/1.09         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['16', '17'])).
% 0.91/1.09  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['3', '6'])).
% 0.91/1.09  thf('20', plain,
% 0.91/1.09      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.91/1.09      inference('demod', [status(thm)], ['18', '19'])).
% 0.91/1.09  thf(t41_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.09       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.09  thf('21', plain,
% 0.91/1.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.91/1.09           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.09  thf(t39_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('22', plain,
% 0.91/1.09      (![X17 : $i, X18 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.91/1.09           = (k2_xboole_0 @ X17 @ X18))),
% 0.91/1.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.09  thf('23', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.09           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.09  thf('24', plain,
% 0.91/1.09      (((k2_xboole_0 @ sk_C_2 @ k1_xboole_0)
% 0.91/1.09         = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['20', '23'])).
% 0.91/1.09  thf('25', plain,
% 0.91/1.09      (![X20 : $i, X21 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.91/1.09           = (k4_xboole_0 @ X20 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.09  thf('26', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf('27', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['25', '26'])).
% 0.91/1.09  thf('28', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.09  thf('30', plain,
% 0.91/1.09      (((sk_C_2) = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.09      inference('demod', [status(thm)], ['24', '29'])).
% 0.91/1.09  thf('31', plain,
% 0.91/1.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.91/1.09           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.09  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['3', '6'])).
% 0.91/1.09  thf('33', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.91/1.09           = (k1_xboole_0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.09  thf('34', plain,
% 0.91/1.09      (![X17 : $i, X18 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.91/1.09           = (k2_xboole_0 @ X17 @ X18))),
% 0.91/1.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.09  thf('35', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf('36', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('37', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.91/1.09           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['35', '36'])).
% 0.91/1.09  thf('38', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf('39', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.09  thf('40', plain,
% 0.91/1.09      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.91/1.09         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.91/1.09          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.91/1.09      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.09  thf('41', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         (~ (r2_hidden @ X2 @ X0)
% 0.91/1.09          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.09  thf('42', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_2)
% 0.91/1.09          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['30', '41'])).
% 0.91/1.09  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['3', '6'])).
% 0.91/1.09  thf('44', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.09           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.09  thf('45', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.91/1.09           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['43', '44'])).
% 0.91/1.09  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.09  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.09  thf('47', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.09  thf('48', plain,
% 0.91/1.09      (![X20 : $i, X21 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.91/1.09           = (k4_xboole_0 @ X20 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.09  thf('49', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.91/1.09           = (k4_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('sup+', [status(thm)], ['47', '48'])).
% 0.91/1.09  thf('50', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.91/1.09  thf('51', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.09  thf('52', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X0 @ X1)
% 0.91/1.09           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['50', '51'])).
% 0.91/1.09  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.09  thf('53', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.09  thf('54', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X0 @ X1)
% 0.91/1.09           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.09      inference('demod', [status(thm)], ['52', '53'])).
% 0.91/1.09  thf('55', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.09  thf('56', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.09  thf('57', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('58', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.91/1.09  thf('59', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.09  thf(t7_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('60', plain,
% 0.91/1.09      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.91/1.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.09  thf('61', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['59', '60'])).
% 0.91/1.09  thf('62', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.91/1.09      inference('sup+', [status(thm)], ['58', '61'])).
% 0.91/1.09  thf('63', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.91/1.09      inference('sup+', [status(thm)], ['57', '62'])).
% 0.91/1.09  thf('64', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.09      inference('sup+', [status(thm)], ['56', '63'])).
% 0.91/1.09  thf('65', plain,
% 0.91/1.09      (![X15 : $i, X16 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('66', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['64', '65'])).
% 0.91/1.09  thf('67', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.09  thf('68', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.09  thf('69', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('70', plain,
% 0.91/1.09      (![X8 : $i, X9 : $i]:
% 0.91/1.09         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.09  thf('71', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.91/1.09  thf('72', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.09  thf('73', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.09  thf('74', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('75', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('76', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['74', '75'])).
% 0.91/1.09  thf('77', plain,
% 0.91/1.09      (((k4_xboole_0 @ sk_C_2 @ k1_xboole_0)
% 0.91/1.09         = (k3_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['73', '76'])).
% 0.91/1.09  thf('78', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.91/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.09  thf('79', plain,
% 0.91/1.09      (((sk_C_2) = (k3_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A)))),
% 0.91/1.09      inference('demod', [status(thm)], ['77', '78'])).
% 0.91/1.09  thf('80', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.09      inference('sup+', [status(thm)], ['56', '63'])).
% 0.91/1.09  thf('81', plain, ((r1_tarski @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.91/1.09      inference('sup+', [status(thm)], ['79', '80'])).
% 0.91/1.09  thf('82', plain,
% 0.91/1.09      (![X15 : $i, X16 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('83', plain,
% 0.91/1.09      (((k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A))
% 0.91/1.09         = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.91/1.09      inference('sup-', [status(thm)], ['81', '82'])).
% 0.91/1.09  thf('84', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.91/1.09  thf('85', plain, (((sk_C_2) = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.91/1.09      inference('demod', [status(thm)], ['83', '84'])).
% 0.91/1.09  thf('86', plain,
% 0.91/1.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.91/1.09           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.09  thf('87', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ sk_C_2 @ X0)
% 0.91/1.09           = (k4_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['85', '86'])).
% 0.91/1.09  thf('88', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_A))
% 0.91/1.09           = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.91/1.09      inference('sup+', [status(thm)], ['68', '87'])).
% 0.91/1.09  thf('89', plain, (((sk_C_2) = (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.91/1.09      inference('demod', [status(thm)], ['83', '84'])).
% 0.91/1.09  thf('90', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_A)) = (sk_C_2))),
% 0.91/1.09      inference('demod', [status(thm)], ['88', '89'])).
% 0.91/1.09  thf('91', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.91/1.09           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.09  thf('92', plain,
% 0.91/1.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.91/1.09           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.09  thf('93', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.91/1.09           = (k3_xboole_0 @ X25 @ X26))),
% 0.91/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.09  thf('94', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X2 @ 
% 0.91/1.09           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.91/1.09           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['92', '93'])).
% 0.91/1.09  thf('95', plain,
% 0.91/1.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.91/1.09           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.09  thf('96', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X2 @ 
% 0.91/1.09           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.91/1.09           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['94', '95'])).
% 0.91/1.09  thf('97', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.91/1.09           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['91', '96'])).
% 0.91/1.09  thf('98', plain,
% 0.91/1.09      (![X20 : $i, X21 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.91/1.09           = (k4_xboole_0 @ X20 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.09  thf('99', plain,
% 0.91/1.09      (![X17 : $i, X18 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.91/1.09           = (k2_xboole_0 @ X17 @ X18))),
% 0.91/1.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.09  thf('100', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['98', '99'])).
% 0.91/1.09  thf('101', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['59', '60'])).
% 0.91/1.09  thf('102', plain,
% 0.91/1.09      (![X15 : $i, X16 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('103', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['101', '102'])).
% 0.91/1.09  thf('104', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['100', '103'])).
% 0.91/1.09  thf('105', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.09  thf('106', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['97', '104', '105'])).
% 0.91/1.09  thf('107', plain,
% 0.91/1.09      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.91/1.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.09  thf('108', plain,
% 0.91/1.09      (![X15 : $i, X16 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('109', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['107', '108'])).
% 0.91/1.09  thf('110', plain,
% 0.91/1.09      (![X20 : $i, X21 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.91/1.09           = (k4_xboole_0 @ X20 @ X21))),
% 0.91/1.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.09  thf('111', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.09           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['109', '110'])).
% 0.91/1.09  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['3', '6'])).
% 0.91/1.09  thf('113', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['111', '112'])).
% 0.91/1.09  thf('114', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['106', '113'])).
% 0.91/1.09  thf('115', plain,
% 0.91/1.09      (![X8 : $i, X10 : $i]:
% 0.91/1.09         ((r1_xboole_0 @ X8 @ X10)
% 0.91/1.09          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.91/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.09  thf('116', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.09          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['114', '115'])).
% 0.91/1.09  thf('117', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('simplify', [status(thm)], ['116'])).
% 0.91/1.09  thf('118', plain,
% 0.91/1.09      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_2)),
% 0.91/1.09      inference('sup+', [status(thm)], ['90', '117'])).
% 0.91/1.09  thf('119', plain,
% 0.91/1.09      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C_2)),
% 0.91/1.09      inference('sup+', [status(thm)], ['55', '118'])).
% 0.91/1.09  thf('120', plain,
% 0.91/1.09      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_2)),
% 0.91/1.09      inference('sup+', [status(thm)], ['54', '119'])).
% 0.91/1.09  thf('121', plain,
% 0.91/1.09      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.09      inference('demod', [status(thm)], ['42', '120'])).
% 0.91/1.09  thf('122', plain,
% 0.91/1.09      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.09      inference('sup-', [status(thm)], ['13', '121'])).
% 0.91/1.09  thf('123', plain,
% 0.91/1.09      (![X8 : $i, X9 : $i]:
% 0.91/1.09         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.09  thf('124', plain,
% 0.91/1.09      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.91/1.09         (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['122', '123'])).
% 0.91/1.09  thf('125', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.09  thf('126', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.91/1.09      inference('demod', [status(thm)], ['124', '125'])).
% 0.91/1.09  thf('127', plain,
% 0.91/1.09      (![X17 : $i, X18 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.91/1.09           = (k2_xboole_0 @ X17 @ X18))),
% 0.91/1.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.09  thf('128', plain,
% 0.91/1.09      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.91/1.09      inference('sup+', [status(thm)], ['126', '127'])).
% 0.91/1.09  thf('129', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.09  thf('130', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.91/1.09      inference('demod', [status(thm)], ['128', '129'])).
% 0.91/1.09  thf('131', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['59', '60'])).
% 0.91/1.09  thf('132', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.91/1.09      inference('sup+', [status(thm)], ['130', '131'])).
% 0.91/1.09  thf('133', plain, ($false), inference('demod', [status(thm)], ['0', '132'])).
% 0.91/1.09  
% 0.91/1.09  % SZS output end Refutation
% 0.91/1.09  
% 0.91/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
