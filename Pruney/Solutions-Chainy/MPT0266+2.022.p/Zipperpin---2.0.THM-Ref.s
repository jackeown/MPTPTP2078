%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JP6I6n3gUV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:46 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 142 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  625 (1040 expanded)
%              Number of equality atoms :   62 ( 111 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['28','31'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('42',plain,(
    ! [X69: $i,X70: $i] :
      ( ( r1_tarski @ X69 @ ( k3_tarski @ X70 ) )
      | ~ ( r2_hidden @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X71 @ X72 ) )
      = ( k2_xboole_0 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( r2_hidden @ X73 @ X74 )
      | ~ ( r1_tarski @ ( k2_tarski @ X73 @ X75 ) @ X74 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X69: $i,X70: $i] :
      ( ( r1_tarski @ X69 @ ( k3_tarski @ X70 ) )
      | ~ ( r2_hidden @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X71 @ X72 ) )
      = ( k2_xboole_0 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( r2_hidden @ X73 @ X74 )
      | ~ ( r1_tarski @ ( k2_tarski @ X73 @ X75 ) @ X74 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['32','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JP6I6n3gUV
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 10:41:22 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 857 iterations in 0.514s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.77/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.77/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.99  thf(t63_zfmisc_1, conjecture,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.77/0.99       ( r2_hidden @ A @ C ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.99        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.77/0.99          ( r2_hidden @ A @ C ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.77/0.99  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_tarski @ sk_A @ sk_B))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(t92_xboole_1, axiom,
% 0.77/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.77/0.99  thf('2', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.77/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.99  thf(t95_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k3_xboole_0 @ A @ B ) =
% 0.77/0.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X8 @ X9)
% 0.77/0.99           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X9)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.77/0.99  thf(t91_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.77/0.99           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X8 @ X9)
% 0.77/0.99           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ (k2_xboole_0 @ X8 @ X9))))),
% 0.77/0.99      inference('demod', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.77/0.99           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.77/0.99           = (k5_xboole_0 @ X1 @ 
% 0.77/0.99              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['5', '6'])).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.77/0.99           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.77/0.99           = (k5_xboole_0 @ X1 @ 
% 0.77/0.99              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 0.77/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.99  thf('10', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.77/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['2', '9'])).
% 0.77/0.99  thf(idempotence_k2_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.99  thf('11', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X8 @ X9)
% 0.77/0.99           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ (k2_xboole_0 @ X8 @ X9))))),
% 0.77/0.99      inference('demod', [status(thm)], ['3', '4'])).
% 0.77/0.99  thf('13', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X0 @ X0)
% 0.77/0.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['11', '12'])).
% 0.77/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.99  thf('14', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/0.99  thf('15', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.77/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.99  thf('16', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.77/0.99           = (k5_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['10', '16'])).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.77/0.99         (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.77/0.99         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.77/0.99      inference('sup+', [status(thm)], ['1', '17'])).
% 0.77/0.99  thf(commutativity_k5_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.77/0.99         (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.77/0.99         = (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.77/0.99      inference('demod', [status(thm)], ['18', '19'])).
% 0.77/0.99  thf('21', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.77/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/0.99  thf('22', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.77/0.99           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.99  thf('24', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.99      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.77/0.99  thf('25', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/0.99  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['24', '25'])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['23', '26'])).
% 0.77/0.99  thf('28', plain,
% 0.77/0.99      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.77/0.99         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.77/0.99            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['20', '27'])).
% 0.77/0.99  thf('29', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['23', '26'])).
% 0.77/0.99  thf('31', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['29', '30'])).
% 0.77/0.99  thf('32', plain,
% 0.77/0.99      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['28', '31'])).
% 0.77/0.99  thf(t70_enumset1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (![X42 : $i, X43 : $i]:
% 0.77/0.99         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.77/0.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.99  thf(t69_enumset1, axiom,
% 0.77/0.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/0.99  thf('34', plain,
% 0.77/0.99      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.77/0.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/0.99  thf(d1_enumset1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.99       ( ![E:$i]:
% 0.77/0.99         ( ( r2_hidden @ E @ D ) <=>
% 0.77/0.99           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.77/0.99  thf(zf_stmt_2, axiom,
% 0.77/0.99    (![E:$i,C:$i,B:$i,A:$i]:
% 0.77/0.99     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.77/0.99       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_3, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.99       ( ![E:$i]:
% 0.77/0.99         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.77/0.99  thf('36', plain,
% 0.77/0.99      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.99         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.77/0.99          | (r2_hidden @ X15 @ X19)
% 0.77/0.99          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.99  thf('37', plain,
% 0.77/0.99      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.99         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.77/0.99          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.77/0.99      inference('simplify', [status(thm)], ['36'])).
% 0.77/0.99  thf('38', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.77/0.99          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['35', '37'])).
% 0.77/0.99  thf('39', plain,
% 0.77/0.99      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.99         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.99  thf('40', plain,
% 0.77/0.99      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.77/0.99         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.77/0.99      inference('simplify', [status(thm)], ['39'])).
% 0.77/0.99  thf('41', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['38', '40'])).
% 0.77/0.99  thf(l49_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.77/0.99  thf('42', plain,
% 0.77/0.99      (![X69 : $i, X70 : $i]:
% 0.77/0.99         ((r1_tarski @ X69 @ (k3_tarski @ X70)) | ~ (r2_hidden @ X69 @ X70))),
% 0.77/0.99      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_tarski @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/0.99  thf('44', plain,
% 0.77/0.99      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.77/0.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.99  thf(l51_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (![X71 : $i, X72 : $i]:
% 0.77/0.99         ((k3_tarski @ (k2_tarski @ X71 @ X72)) = (k2_xboole_0 @ X71 @ X72))),
% 0.77/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('47', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.99  thf('48', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['46', '47'])).
% 0.77/0.99  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.77/0.99      inference('demod', [status(thm)], ['43', '48'])).
% 0.77/0.99  thf(t38_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.77/0.99       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.77/0.99  thf('50', plain,
% 0.77/0.99      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.77/0.99         ((r2_hidden @ X73 @ X74)
% 0.77/0.99          | ~ (r1_tarski @ (k2_tarski @ X73 @ X75) @ X74))),
% 0.77/0.99      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.77/0.99  thf('51', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('52', plain,
% 0.77/0.99      (![X69 : $i, X70 : $i]:
% 0.77/0.99         ((r1_tarski @ X69 @ (k3_tarski @ X70)) | ~ (r2_hidden @ X69 @ X70))),
% 0.77/0.99      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.77/0.99  thf('53', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.99  thf('54', plain,
% 0.77/0.99      (![X71 : $i, X72 : $i]:
% 0.77/0.99         ((k3_tarski @ (k2_tarski @ X71 @ X72)) = (k2_xboole_0 @ X71 @ X72))),
% 0.77/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.99  thf('55', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.99  thf('56', plain,
% 0.77/0.99      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.77/0.99         ((r2_hidden @ X73 @ X74)
% 0.77/0.99          | ~ (r1_tarski @ (k2_tarski @ X73 @ X75) @ X74))),
% 0.77/0.99      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.77/0.99  thf('57', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         (r2_hidden @ X2 @ (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/0.99  thf('58', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.77/0.99      inference('sup+', [status(thm)], ['32', '57'])).
% 0.77/0.99  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
