%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJVv14gXZr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 184 expanded)
%              Number of leaves         :   26 (  68 expanded)
%              Depth                    :   22
%              Number of atoms          :  773 (1359 expanded)
%              Number of equality atoms :   60 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) )
        = X35 )
      | ( r2_hidden @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_xboole_0 @ X25 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_xboole_0 @ X25 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65','78'])).

thf('80',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','84'])).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('88',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJVv14gXZr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/1.01  % Solved by: fo/fo7.sh
% 0.76/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.01  % done 2083 iterations in 0.559s
% 0.76/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/1.01  % SZS output start Refutation
% 0.76/1.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.76/1.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.01  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(t149_zfmisc_1, conjecture,
% 0.76/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.01     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.76/1.01         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.76/1.01       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.76/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.01        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.76/1.01            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.76/1.01          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.76/1.01    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.76/1.01  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf(d7_xboole_0, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.76/1.01       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.76/1.01  thf('2', plain,
% 0.76/1.01      (![X2 : $i, X3 : $i]:
% 0.76/1.01         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/1.01  thf('4', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.01  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.76/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.76/1.01  thf('6', plain,
% 0.76/1.01      (![X2 : $i, X4 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('7', plain,
% 0.76/1.01      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/1.01  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.76/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.76/1.01  thf(t65_zfmisc_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/1.01       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.76/1.01  thf('9', plain,
% 0.76/1.01      (![X35 : $i, X36 : $i]:
% 0.76/1.01         (((k4_xboole_0 @ X35 @ (k1_tarski @ X36)) = (X35))
% 0.76/1.01          | (r2_hidden @ X36 @ X35))),
% 0.76/1.01      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.76/1.01  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.76/1.01  thf('10', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.76/1.01      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.76/1.01  thf(t83_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/1.01  thf('11', plain,
% 0.76/1.01      (![X22 : $i, X23 : $i]:
% 0.76/1.01         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.76/1.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.76/1.01  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.01  thf(t36_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/1.01  thf('13', plain,
% 0.76/1.01      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.76/1.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/1.01  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/1.01      inference('sup+', [status(thm)], ['12', '13'])).
% 0.76/1.01  thf(t85_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.76/1.01  thf('15', plain,
% 0.76/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/1.01         (~ (r1_tarski @ X25 @ X26)
% 0.76/1.01          | (r1_xboole_0 @ X25 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.76/1.01  thf('16', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/1.01  thf('17', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['9', '16'])).
% 0.76/1.01  thf(t70_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.76/1.01            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.76/1.01       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.76/1.01            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.76/1.01  thf('18', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X16 @ X17)
% 0.76/1.01          | ~ (r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X19)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/1.01  thf('19', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.76/1.01          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/1.01  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('21', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('22', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.76/1.01          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.76/1.01          | ~ (r1_xboole_0 @ X16 @ X18))),
% 0.76/1.01      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/1.01  thf('23', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.76/1.01          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/1.01  thf('24', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.76/1.01      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/1.01  thf('25', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf(t3_xboole_0, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.76/1.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.76/1.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.76/1.01            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.76/1.01  thf('26', plain,
% 0.76/1.01      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X7 @ X5)
% 0.76/1.01          | ~ (r2_hidden @ X7 @ X8)
% 0.76/1.01          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.76/1.01      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/1.01  thf('27', plain,
% 0.76/1.01      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/1.01  thf('28', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.76/1.01      inference('sup-', [status(thm)], ['24', '27'])).
% 0.76/1.01  thf('29', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.76/1.01      inference('sup-', [status(thm)], ['19', '28'])).
% 0.76/1.01  thf('30', plain,
% 0.76/1.01      (![X2 : $i, X3 : $i]:
% 0.76/1.01         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('31', plain,
% 0.76/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/1.01  thf('32', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.01  thf('33', plain,
% 0.76/1.01      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.76/1.01      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/1.01  thf(t100_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/1.01  thf('34', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.76/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/1.01  thf('35', plain,
% 0.76/1.01      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D))
% 0.76/1.01         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/1.01  thf('36', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.76/1.01      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.76/1.01  thf('37', plain,
% 0.76/1.01      (![X2 : $i, X3 : $i]:
% 0.76/1.01         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('38', plain,
% 0.76/1.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/1.01  thf('39', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.76/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/1.01  thf('40', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['38', '39'])).
% 0.76/1.01  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.01  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['40', '41'])).
% 0.76/1.01  thf('43', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 0.76/1.01      inference('demod', [status(thm)], ['35', '42'])).
% 0.76/1.01  thf('44', plain,
% 0.76/1.01      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('45', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.01  thf('46', plain,
% 0.76/1.01      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.76/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.76/1.01  thf('47', plain,
% 0.76/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/1.01         (~ (r1_tarski @ X25 @ X26)
% 0.76/1.01          | (r1_xboole_0 @ X25 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.76/1.01  thf('48', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.76/1.01          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/1.01  thf('49', plain,
% 0.76/1.01      (![X2 : $i, X3 : $i]:
% 0.76/1.01         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('50', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.76/1.01           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D))) = (k1_xboole_0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['48', '49'])).
% 0.76/1.01  thf('51', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.01  thf('52', plain,
% 0.76/1.01      (![X2 : $i, X4 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('53', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['51', '52'])).
% 0.76/1.01  thf('54', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.76/1.01          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.76/1.01             (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['50', '53'])).
% 0.76/1.01  thf('55', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.76/1.01          (k3_xboole_0 @ sk_B @ sk_A))),
% 0.76/1.01      inference('simplify', [status(thm)], ['54'])).
% 0.76/1.01  thf('56', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.76/1.01      inference('sup+', [status(thm)], ['43', '55'])).
% 0.76/1.01  thf('57', plain,
% 0.76/1.01      (![X22 : $i, X23 : $i]:
% 0.76/1.01         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.76/1.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.76/1.01  thf('58', plain,
% 0.76/1.01      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 0.76/1.01      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/1.01  thf(t48_xboole_1, axiom,
% 0.76/1.01    (![A:$i,B:$i]:
% 0.76/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/1.01  thf('59', plain,
% 0.76/1.01      (![X13 : $i, X14 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.76/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.01  thf('60', plain,
% 0.76/1.01      (![X13 : $i, X14 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.76/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.01  thf('61', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/1.01           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.76/1.01  thf('62', plain,
% 0.76/1.01      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 0.76/1.01      inference('demod', [status(thm)], ['58', '61'])).
% 0.76/1.01  thf('63', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.76/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/1.01  thf('64', plain,
% 0.76/1.01      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))
% 0.76/1.01         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.76/1.01      inference('sup+', [status(thm)], ['62', '63'])).
% 0.76/1.01  thf('65', plain,
% 0.76/1.01      (![X13 : $i, X14 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.76/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.01  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.01  thf('67', plain,
% 0.76/1.01      (![X13 : $i, X14 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.76/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.01  thf('68', plain,
% 0.76/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['66', '67'])).
% 0.76/1.01  thf('69', plain,
% 0.76/1.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/1.01  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/1.01      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/1.01  thf('71', plain,
% 0.76/1.01      (![X13 : $i, X14 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.76/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.76/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.01  thf('72', plain,
% 0.76/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['70', '71'])).
% 0.76/1.01  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/1.01  thf('74', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.76/1.01      inference('demod', [status(thm)], ['72', '73'])).
% 0.76/1.01  thf('75', plain,
% 0.76/1.01      (![X9 : $i, X10 : $i]:
% 0.76/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.76/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.76/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/1.01  thf('76', plain,
% 0.76/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['74', '75'])).
% 0.76/1.01  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/1.01      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/1.01  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/1.01      inference('sup+', [status(thm)], ['76', '77'])).
% 0.76/1.01  thf('79', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.76/1.01      inference('demod', [status(thm)], ['64', '65', '78'])).
% 0.76/1.01  thf('80', plain,
% 0.76/1.01      (![X2 : $i, X4 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.76/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/1.01  thf('81', plain,
% 0.76/1.01      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.76/1.01      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/1.01  thf('82', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.76/1.01      inference('simplify', [status(thm)], ['81'])).
% 0.76/1.01  thf('83', plain,
% 0.76/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.76/1.01          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.76/1.01          | ~ (r1_xboole_0 @ X16 @ X18))),
% 0.76/1.01      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/1.01  thf('84', plain,
% 0.76/1.01      (![X0 : $i]:
% 0.76/1.01         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.76/1.01          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['82', '83'])).
% 0.76/1.01  thf('85', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['8', '84'])).
% 0.76/1.01  thf('86', plain,
% 0.76/1.01      (![X5 : $i, X6 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.76/1.01      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/1.01  thf('87', plain,
% 0.76/1.01      (![X5 : $i, X6 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.76/1.01      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/1.01  thf('88', plain,
% 0.76/1.01      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X7 @ X5)
% 0.76/1.01          | ~ (r2_hidden @ X7 @ X8)
% 0.76/1.01          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.76/1.01      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/1.01  thf('89', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X1 @ X0)
% 0.76/1.01          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/1.01          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.76/1.01      inference('sup-', [status(thm)], ['87', '88'])).
% 0.76/1.01  thf('90', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         ((r1_xboole_0 @ X0 @ X1)
% 0.76/1.01          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.76/1.01          | (r1_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['86', '89'])).
% 0.76/1.01  thf('91', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.76/1.01      inference('simplify', [status(thm)], ['90'])).
% 0.76/1.01  thf('92', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.76/1.01      inference('sup-', [status(thm)], ['85', '91'])).
% 0.76/1.01  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.76/1.01  
% 0.76/1.01  % SZS output end Refutation
% 0.76/1.01  
% 0.87/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
