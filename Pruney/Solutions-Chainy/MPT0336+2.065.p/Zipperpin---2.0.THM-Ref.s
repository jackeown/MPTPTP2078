%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BNOFDLw62O

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 3.65s
% Output     : Refutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 327 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   27
%              Number of atoms          : 1006 (2724 expanded)
%              Number of equality atoms :   77 ( 210 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('34',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['45','55','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('90',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','99'])).

thf('101',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','100'])).

thf('102',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','106'])).

thf('108',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('109',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BNOFDLw62O
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:22:08 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 3.65/3.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.65/3.84  % Solved by: fo/fo7.sh
% 3.65/3.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.65/3.84  % done 7281 iterations in 3.354s
% 3.65/3.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.65/3.84  % SZS output start Refutation
% 3.65/3.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.65/3.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.65/3.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.65/3.84  thf(sk_D_type, type, sk_D: $i).
% 3.65/3.84  thf(sk_B_type, type, sk_B: $i).
% 3.65/3.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.65/3.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.65/3.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.65/3.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.65/3.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.65/3.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.65/3.84  thf(sk_A_type, type, sk_A: $i).
% 3.65/3.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.65/3.84  thf(t149_zfmisc_1, conjecture,
% 3.65/3.84    (![A:$i,B:$i,C:$i,D:$i]:
% 3.65/3.84     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.65/3.84         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.65/3.84       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.65/3.84  thf(zf_stmt_0, negated_conjecture,
% 3.65/3.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.65/3.84        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.65/3.84            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.65/3.84          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 3.65/3.84    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 3.65/3.84  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf(d7_xboole_0, axiom,
% 3.65/3.84    (![A:$i,B:$i]:
% 3.65/3.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.65/3.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.65/3.84  thf('2', plain,
% 3.65/3.84      (![X2 : $i, X3 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['1', '2'])).
% 3.65/3.84  thf(commutativity_k3_xboole_0, axiom,
% 3.65/3.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.65/3.84  thf('4', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['3', '4'])).
% 3.65/3.84  thf('6', plain,
% 3.65/3.84      (![X2 : $i, X4 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('7', plain,
% 3.65/3.84      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 3.65/3.84      inference('sup-', [status(thm)], ['5', '6'])).
% 3.65/3.84  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 3.65/3.84      inference('simplify', [status(thm)], ['7'])).
% 3.65/3.84  thf('9', plain,
% 3.65/3.84      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf('10', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('11', plain,
% 3.65/3.84      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 3.65/3.84      inference('demod', [status(thm)], ['9', '10'])).
% 3.65/3.84  thf(t28_xboole_1, axiom,
% 3.65/3.84    (![A:$i,B:$i]:
% 3.65/3.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.65/3.84  thf('12', plain,
% 3.65/3.84      (![X16 : $i, X17 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 3.65/3.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.65/3.84  thf('13', plain,
% 3.65/3.84      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 3.65/3.84         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('sup-', [status(thm)], ['11', '12'])).
% 3.65/3.84  thf('14', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('15', plain,
% 3.65/3.84      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 3.65/3.84         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('demod', [status(thm)], ['13', '14'])).
% 3.65/3.84  thf(t16_xboole_1, axiom,
% 3.65/3.84    (![A:$i,B:$i,C:$i]:
% 3.65/3.84     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 3.65/3.84       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.65/3.84  thf('16', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('17', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('18', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.65/3.84           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['16', '17'])).
% 3.65/3.84  thf('19', plain,
% 3.65/3.84      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))
% 3.65/3.84         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('demod', [status(thm)], ['15', '18'])).
% 3.65/3.84  thf('20', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf(t65_zfmisc_1, axiom,
% 3.65/3.84    (![A:$i,B:$i]:
% 3.65/3.84     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.65/3.84       ( ~( r2_hidden @ B @ A ) ) ))).
% 3.65/3.84  thf('21', plain,
% 3.65/3.84      (![X37 : $i, X38 : $i]:
% 3.65/3.84         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 3.65/3.84          | (r2_hidden @ X38 @ X37))),
% 3.65/3.84      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.65/3.84  thf(t79_xboole_1, axiom,
% 3.65/3.84    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.65/3.84  thf('22', plain,
% 3.65/3.84      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 3.65/3.84      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.65/3.84  thf(symmetry_r1_xboole_0, axiom,
% 3.65/3.84    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.65/3.84  thf('23', plain,
% 3.65/3.84      (![X5 : $i, X6 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.65/3.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.65/3.84  thf('24', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['22', '23'])).
% 3.65/3.84  thf('25', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 3.65/3.84      inference('sup+', [status(thm)], ['21', '24'])).
% 3.65/3.84  thf(t70_xboole_1, axiom,
% 3.65/3.84    (![A:$i,B:$i,C:$i]:
% 3.65/3.84     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.65/3.84            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.65/3.84       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.65/3.84            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 3.65/3.84  thf('26', plain,
% 3.65/3.84      (![X18 : $i, X19 : $i, X21 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X18 @ X19)
% 3.65/3.84          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.65/3.84  thf('27', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.65/3.84          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 3.65/3.84      inference('sup-', [status(thm)], ['25', '26'])).
% 3.65/3.84  thf('28', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf('29', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf('30', plain,
% 3.65/3.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 3.65/3.84          | ~ (r1_xboole_0 @ X18 @ X19)
% 3.65/3.84          | ~ (r1_xboole_0 @ X18 @ X20))),
% 3.65/3.84      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.65/3.84  thf('31', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 3.65/3.84          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['29', '30'])).
% 3.65/3.84  thf('32', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 3.65/3.84      inference('sup-', [status(thm)], ['28', '31'])).
% 3.65/3.84  thf('33', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 3.65/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.65/3.84  thf(t3_xboole_0, axiom,
% 3.65/3.84    (![A:$i,B:$i]:
% 3.65/3.84     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.65/3.84            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.65/3.84       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.65/3.84            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.65/3.84  thf('34', plain,
% 3.65/3.84      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.65/3.84         (~ (r2_hidden @ X9 @ X7)
% 3.65/3.84          | ~ (r2_hidden @ X9 @ X10)
% 3.65/3.84          | ~ (r1_xboole_0 @ X7 @ X10))),
% 3.65/3.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.65/3.84  thf('35', plain,
% 3.65/3.84      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['33', '34'])).
% 3.65/3.84  thf('36', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 3.65/3.84      inference('sup-', [status(thm)], ['32', '35'])).
% 3.65/3.84  thf('37', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 3.65/3.84      inference('sup-', [status(thm)], ['27', '36'])).
% 3.65/3.84  thf('38', plain,
% 3.65/3.84      (![X2 : $i, X3 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('39', plain,
% 3.65/3.84      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['37', '38'])).
% 3.65/3.84  thf('40', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('41', plain,
% 3.65/3.84      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['39', '40'])).
% 3.65/3.84  thf('42', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('43', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('44', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.65/3.84           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['42', '43'])).
% 3.65/3.84  thf('45', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 3.65/3.84           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['41', '44'])).
% 3.65/3.84  thf('46', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 3.65/3.84      inference('simplify', [status(thm)], ['7'])).
% 3.65/3.84  thf(t74_xboole_1, axiom,
% 3.65/3.84    (![A:$i,B:$i,C:$i]:
% 3.65/3.84     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 3.65/3.84          ( r1_xboole_0 @ A @ B ) ) ))).
% 3.65/3.84  thf('47', plain,
% 3.65/3.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.65/3.84         (~ (r1_xboole_0 @ X22 @ X23)
% 3.65/3.84          | (r1_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t74_xboole_1])).
% 3.65/3.84  thf('48', plain,
% 3.65/3.84      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['46', '47'])).
% 3.65/3.84  thf('49', plain,
% 3.65/3.84      (![X2 : $i, X3 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('50', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)) = (k1_xboole_0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['48', '49'])).
% 3.65/3.84  thf('51', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('52', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 3.65/3.84           = (k3_xboole_0 @ sk_B @ 
% 3.65/3.84              (k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X1) @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['50', '51'])).
% 3.65/3.84  thf('53', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('54', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)) = (k1_xboole_0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['48', '49'])).
% 3.65/3.84  thf('55', plain,
% 3.65/3.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.65/3.84  thf('56', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.65/3.84           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['16', '17'])).
% 3.65/3.84  thf('57', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k1_xboole_0)
% 3.65/3.84           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D))))),
% 3.65/3.84      inference('demod', [status(thm)], ['45', '55', '56'])).
% 3.65/3.84  thf('58', plain,
% 3.65/3.84      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 3.65/3.84         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('demod', [status(thm)], ['13', '14'])).
% 3.65/3.84  thf('59', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('60', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 3.65/3.84           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 3.65/3.84              (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['58', '59'])).
% 3.65/3.84  thf('61', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('62', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('63', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 3.65/3.84           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 3.65/3.84              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 3.65/3.84      inference('demod', [status(thm)], ['60', '61', '62'])).
% 3.65/3.84  thf('64', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.65/3.84           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['16', '17'])).
% 3.65/3.84  thf('65', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.65/3.84           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['42', '43'])).
% 3.65/3.84  thf('66', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 3.65/3.84           = (k3_xboole_0 @ sk_B @ 
% 3.65/3.84              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))))),
% 3.65/3.84      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.65/3.84  thf('67', plain,
% 3.65/3.84      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 3.65/3.84         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 3.65/3.84      inference('sup+', [status(thm)], ['57', '66'])).
% 3.65/3.84  thf('68', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('69', plain,
% 3.65/3.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.65/3.84  thf('70', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('71', plain,
% 3.65/3.84      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.65/3.84      inference('sup+', [status(thm)], ['69', '70'])).
% 3.65/3.84  thf('72', plain,
% 3.65/3.84      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['67', '68', '71'])).
% 3.65/3.84  thf('73', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('74', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('75', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('76', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.65/3.84  thf('77', plain,
% 3.65/3.84      (![X2 : $i, X4 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('78', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('sup-', [status(thm)], ['76', '77'])).
% 3.65/3.84  thf('79', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['75', '78'])).
% 3.65/3.84  thf('80', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['74', '79'])).
% 3.65/3.84  thf('81', plain,
% 3.65/3.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 3.65/3.84           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.65/3.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.65/3.84  thf('82', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 3.65/3.84      inference('demod', [status(thm)], ['80', '81'])).
% 3.65/3.84  thf('83', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['73', '82'])).
% 3.65/3.84  thf('84', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 3.65/3.84             (k3_xboole_0 @ sk_B @ X0)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['72', '83'])).
% 3.65/3.84  thf('85', plain,
% 3.65/3.84      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.65/3.84      inference('sup+', [status(thm)], ['69', '70'])).
% 3.65/3.84  thf('86', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         (((k1_xboole_0) != (k1_xboole_0))
% 3.65/3.84          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 3.65/3.84             (k3_xboole_0 @ sk_B @ X0)))),
% 3.65/3.84      inference('demod', [status(thm)], ['84', '85'])).
% 3.65/3.84  thf('87', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 3.65/3.84      inference('simplify', [status(thm)], ['86'])).
% 3.65/3.84  thf('88', plain,
% 3.65/3.84      (![X7 : $i, X8 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 3.65/3.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.65/3.84  thf('89', plain,
% 3.65/3.84      (![X7 : $i, X8 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 3.65/3.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.65/3.84  thf('90', plain,
% 3.65/3.84      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.65/3.84         (~ (r2_hidden @ X9 @ X7)
% 3.65/3.84          | ~ (r2_hidden @ X9 @ X10)
% 3.65/3.84          | ~ (r1_xboole_0 @ X7 @ X10))),
% 3.65/3.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.65/3.84  thf('91', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X0 @ X1)
% 3.65/3.84          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.65/3.84          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 3.65/3.84      inference('sup-', [status(thm)], ['89', '90'])).
% 3.65/3.84  thf('92', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X0 @ X1)
% 3.65/3.84          | ~ (r1_xboole_0 @ X0 @ X0)
% 3.65/3.84          | (r1_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('sup-', [status(thm)], ['88', '91'])).
% 3.65/3.84  thf('93', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i]:
% 3.65/3.84         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 3.65/3.84      inference('simplify', [status(thm)], ['92'])).
% 3.65/3.84  thf('94', plain,
% 3.65/3.84      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 3.65/3.84      inference('sup-', [status(thm)], ['87', '93'])).
% 3.65/3.84  thf('95', plain,
% 3.65/3.84      (![X2 : $i, X3 : $i]:
% 3.65/3.84         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('96', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0) = (k1_xboole_0))),
% 3.65/3.84      inference('sup-', [status(thm)], ['94', '95'])).
% 3.65/3.84  thf('97', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.65/3.84           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['42', '43'])).
% 3.65/3.84  thf('98', plain,
% 3.65/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.65/3.84           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.65/3.84      inference('sup+', [status(thm)], ['16', '17'])).
% 3.65/3.84  thf('99', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 3.65/3.84      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.65/3.84  thf('100', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 3.65/3.84      inference('sup+', [status(thm)], ['20', '99'])).
% 3.65/3.84  thf('101', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('demod', [status(thm)], ['19', '100'])).
% 3.65/3.84  thf('102', plain,
% 3.65/3.84      (![X2 : $i, X4 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.65/3.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.65/3.84  thf('103', plain,
% 3.65/3.84      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 3.65/3.84      inference('sup-', [status(thm)], ['101', '102'])).
% 3.65/3.84  thf('104', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 3.65/3.84      inference('simplify', [status(thm)], ['103'])).
% 3.65/3.84  thf('105', plain,
% 3.65/3.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 3.65/3.84          | ~ (r1_xboole_0 @ X18 @ X19)
% 3.65/3.84          | ~ (r1_xboole_0 @ X18 @ X20))),
% 3.65/3.84      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.65/3.84  thf('106', plain,
% 3.65/3.84      (![X0 : $i]:
% 3.65/3.84         (~ (r1_xboole_0 @ sk_B @ X0)
% 3.65/3.84          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 3.65/3.84      inference('sup-', [status(thm)], ['104', '105'])).
% 3.65/3.84  thf('107', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 3.65/3.84      inference('sup-', [status(thm)], ['8', '106'])).
% 3.65/3.84  thf('108', plain,
% 3.65/3.84      (![X5 : $i, X6 : $i]:
% 3.65/3.84         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.65/3.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.65/3.84  thf('109', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 3.65/3.84      inference('sup-', [status(thm)], ['107', '108'])).
% 3.65/3.84  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 3.65/3.84  
% 3.65/3.84  % SZS output end Refutation
% 3.65/3.84  
% 3.65/3.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
