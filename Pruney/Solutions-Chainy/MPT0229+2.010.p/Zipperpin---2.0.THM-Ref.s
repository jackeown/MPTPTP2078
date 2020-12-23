%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BQrkOuNbbB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:08 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 324 expanded)
%              Number of leaves         :   33 ( 118 expanded)
%              Depth                    :   23
%              Number of atoms          :  750 (2233 expanded)
%              Number of equality atoms :   85 ( 228 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( X18 = X19 )
      | ( X18 = X20 )
      | ( X18 = X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('9',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','41','42'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_B @ sk_A )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_B @ sk_A )
      = ( k2_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X31 @ X30 @ X29 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_A @ sk_B @ X0 )
      = ( k2_tarski @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('50',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_tarski @ sk_B @ sk_B )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_B @ sk_A )
      = ( k2_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ sk_B ) )
      | ( zip_tseitin_0 @ X1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BQrkOuNbbB
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 373 iterations in 0.152s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.35/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(d1_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.61       ( ![E:$i]:
% 0.35/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, axiom,
% 0.35/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.35/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.61         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.35/0.61          | ((X18) = (X19))
% 0.35/0.61          | ((X18) = (X20))
% 0.35/0.61          | ((X18) = (X21)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(t24_zfmisc_1, conjecture,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.35/0.61       ( ( A ) = ( B ) ) ))).
% 0.35/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i]:
% 0.35/0.61        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.35/0.61          ( ( A ) = ( B ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.35/0.61  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.61  thf(t28_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]:
% 0.35/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.35/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.61         = (k1_tarski @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.61  thf(t100_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X6 : $i, X7 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf('5', plain,
% 0.35/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.61  thf(t98_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.61  thf('6', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X15 @ X16)
% 0.35/0.61           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.35/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.35/0.61            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.35/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.35/0.61  thf(t41_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k2_tarski @ A @ B ) =
% 0.35/0.61       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      (![X32 : $i, X33 : $i]:
% 0.35/0.61         ((k2_tarski @ X32 @ X33)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (((k2_tarski @ sk_B @ sk_A)
% 0.35/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.35/0.61            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.35/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.61  thf(t79_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.35/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.35/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      (![X4 : $i, X5 : $i]:
% 0.35/0.61         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.61  thf(d7_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.35/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.61  thf('14', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.61  thf(t48_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.61  thf('15', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.35/0.61           = (k3_xboole_0 @ X10 @ X11))),
% 0.35/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.35/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.35/0.61          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['14', '17'])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (![X6 : $i, X7 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.35/0.61           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.35/0.61  thf(t5_boole, axiom,
% 0.35/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.61  thf('22', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.35/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.61  thf('24', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.35/0.61      inference('demod', [status(thm)], ['18', '23'])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      (![X6 : $i, X7 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.61           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.35/0.61  thf('29', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.35/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.61  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.35/0.61           = (k3_xboole_0 @ X10 @ X11))),
% 0.35/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.35/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.61  thf('35', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.35/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (![X6 : $i, X7 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.35/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf('37', plain,
% 0.35/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['34', '37', '40'])).
% 0.35/0.61  thf('42', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.35/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.61  thf('43', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['9', '41', '42'])).
% 0.35/0.61  thf(t42_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.35/0.61       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.35/0.61  thf('44', plain,
% 0.35/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X34 @ X35 @ X36)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.35/0.61  thf('45', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X0 @ sk_B @ sk_A)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_B)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['43', '44'])).
% 0.35/0.61  thf('46', plain,
% 0.35/0.61      (![X32 : $i, X33 : $i]:
% 0.35/0.61         ((k2_tarski @ X32 @ X33)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.35/0.61  thf('47', plain,
% 0.35/0.61      (![X0 : $i]: ((k1_enumset1 @ X0 @ sk_B @ sk_A) = (k2_tarski @ X0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.35/0.61  thf(t102_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.35/0.61  thf('48', plain,
% 0.35/0.61      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X31 @ X30 @ X29) = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.35/0.61      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.35/0.61  thf('49', plain,
% 0.35/0.61      (![X0 : $i]: ((k1_enumset1 @ sk_A @ sk_B @ X0) = (k2_tarski @ X0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['47', '48'])).
% 0.35/0.61  thf(t69_enumset1, axiom,
% 0.35/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.61  thf('50', plain,
% 0.35/0.61      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.35/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.61  thf('51', plain,
% 0.35/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X34 @ X35 @ X36)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['50', '51'])).
% 0.35/0.61  thf('53', plain,
% 0.35/0.61      (![X32 : $i, X33 : $i]:
% 0.35/0.61         ((k2_tarski @ X32 @ X33)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.35/0.61  thf('54', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.61  thf('55', plain, (((k2_tarski @ sk_B @ sk_B) = (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['49', '54'])).
% 0.35/0.61  thf('56', plain,
% 0.35/0.61      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.35/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.61  thf('57', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.35/0.61  thf('58', plain,
% 0.35/0.61      (![X0 : $i]: ((k1_enumset1 @ X0 @ sk_B @ sk_A) = (k2_tarski @ X0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.35/0.61  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_3, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.61       ( ![E:$i]:
% 0.35/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.35/0.61  thf('59', plain,
% 0.35/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.61         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.35/0.61          | (r2_hidden @ X22 @ X26)
% 0.35/0.61          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.61  thf('60', plain,
% 0.35/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.35/0.61         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.35/0.61          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.35/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.35/0.61  thf('61', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ sk_B))
% 0.35/0.61          | (zip_tseitin_0 @ X1 @ sk_A @ sk_B @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['58', '60'])).
% 0.35/0.61  thf('62', plain,
% 0.35/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.61         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('63', plain,
% 0.35/0.61      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.35/0.61         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 0.35/0.61      inference('simplify', [status(thm)], ['62'])).
% 0.35/0.61  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['61', '63'])).
% 0.35/0.61  thf('65', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['57', '64'])).
% 0.35/0.61  thf('66', plain,
% 0.35/0.61      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.35/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.61  thf(t70_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.61  thf('67', plain,
% 0.35/0.61      (![X42 : $i, X43 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.35/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.61  thf('68', plain,
% 0.35/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X27 @ X26)
% 0.35/0.61          | ~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.35/0.61          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.61  thf('69', plain,
% 0.35/0.61      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.35/0.61         (~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.35/0.61          | ~ (r2_hidden @ X27 @ (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['68'])).
% 0.35/0.61  thf('70', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.35/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['67', '69'])).
% 0.35/0.61  thf('71', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.35/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['66', '70'])).
% 0.35/0.61  thf('72', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.35/0.61      inference('sup-', [status(thm)], ['65', '71'])).
% 0.35/0.61  thf('73', plain,
% 0.35/0.61      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '72'])).
% 0.35/0.61  thf('74', plain, (((sk_A) = (sk_B))),
% 0.35/0.61      inference('simplify', [status(thm)], ['73'])).
% 0.35/0.61  thf('75', plain, (((sk_A) != (sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.61  thf('76', plain, ($false),
% 0.35/0.61      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
