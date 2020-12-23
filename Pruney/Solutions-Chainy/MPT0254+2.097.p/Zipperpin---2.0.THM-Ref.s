%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WgQE9UD21I

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:48 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  140 (1390 expanded)
%              Number of leaves         :   32 ( 517 expanded)
%              Depth                    :   20
%              Number of atoms          :  965 (11452 expanded)
%              Number of equality atoms :  111 (1353 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('6',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('12',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('13',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','40','41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('57',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('61',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','55','58','59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','55','58','59','60'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','55','58','59','60'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('75',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('80',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('82',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('83',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['81','92'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('94',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','95'])).

thf('97',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','95'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('103',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['17','96','97','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WgQE9UD21I
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.43/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.69  % Solved by: fo/fo7.sh
% 0.43/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.69  % done 537 iterations in 0.242s
% 0.43/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.69  % SZS output start Refutation
% 0.43/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.69  thf(t100_xboole_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.69  thf('0', plain,
% 0.43/0.69      (![X12 : $i, X13 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.43/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.69  thf(commutativity_k5_xboole_0, axiom,
% 0.43/0.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.43/0.69  thf('1', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf(t5_boole, axiom,
% 0.43/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.69  thf('2', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.43/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.69  thf('3', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.69  thf('4', plain,
% 0.43/0.69      (![X0 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['0', '3'])).
% 0.43/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.69  thf('5', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.43/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.69  thf('6', plain,
% 0.43/0.69      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.69  thf(t36_xboole_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.69  thf('7', plain,
% 0.43/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.43/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.69  thf('8', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.43/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.43/0.69  thf(d1_zfmisc_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.69  thf('9', plain,
% 0.43/0.69      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.43/0.69         (~ (r1_tarski @ X53 @ X54)
% 0.43/0.69          | (r2_hidden @ X53 @ X55)
% 0.43/0.69          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 0.43/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.69  thf('10', plain,
% 0.43/0.69      (![X53 : $i, X54 : $i]:
% 0.43/0.69         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 0.43/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.69  thf('11', plain, ((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['8', '10'])).
% 0.43/0.69  thf(t1_zfmisc_1, axiom,
% 0.43/0.69    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.43/0.69  thf('12', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.43/0.69  thf('13', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['11', '12'])).
% 0.43/0.69  thf('14', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.43/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.69  thf(t4_xboole_0, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.43/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.43/0.69  thf('15', plain,
% 0.43/0.69      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.43/0.69         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.43/0.69          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.43/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.69  thf('16', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.69  thf('17', plain,
% 0.43/0.69      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['13', '16'])).
% 0.43/0.69  thf(t49_zfmisc_1, conjecture,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.43/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.69    (~( ![A:$i,B:$i]:
% 0.43/0.69        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.43/0.69    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.43/0.69  thf('18', plain,
% 0.43/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf(t94_xboole_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( k2_xboole_0 @ A @ B ) =
% 0.43/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.69  thf('19', plain,
% 0.43/0.69      (![X23 : $i, X24 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.43/0.69           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.43/0.69              (k3_xboole_0 @ X23 @ X24)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.43/0.69  thf('20', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('21', plain,
% 0.43/0.69      (![X23 : $i, X24 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.43/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.43/0.69              (k5_xboole_0 @ X23 @ X24)))),
% 0.43/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.69  thf('22', plain,
% 0.43/0.69      (![X23 : $i, X24 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.43/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.43/0.69              (k5_xboole_0 @ X23 @ X24)))),
% 0.43/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.69  thf('23', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.43/0.69           = (k5_xboole_0 @ 
% 0.43/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.43/0.69              (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.43/0.69  thf('24', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('25', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.43/0.69           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.43/0.69              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.43/0.69      inference('demod', [status(thm)], ['23', '24'])).
% 0.43/0.69  thf('26', plain,
% 0.43/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.43/0.69         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.43/0.69         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.43/0.69            (k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.43/0.69             (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.43/0.69      inference('sup+', [status(thm)], ['18', '25'])).
% 0.43/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.69  thf('27', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.69  thf('28', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('29', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.69  thf('30', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.69  thf('32', plain,
% 0.43/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.69         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.43/0.69      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.43/0.69  thf('33', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('34', plain,
% 0.43/0.69      (![X23 : $i, X24 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.43/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.43/0.69              (k5_xboole_0 @ X23 @ X24)))),
% 0.43/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.69  thf('35', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.43/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.43/0.69  thf('36', plain,
% 0.43/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.69         = (k5_xboole_0 @ 
% 0.43/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.43/0.69            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.43/0.69      inference('sup+', [status(thm)], ['32', '35'])).
% 0.43/0.69  thf(t91_xboole_1, axiom,
% 0.43/0.69    (![A:$i,B:$i,C:$i]:
% 0.43/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.43/0.69  thf('37', plain,
% 0.43/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.43/0.69           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.69  thf('38', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.69  thf('39', plain,
% 0.43/0.69      (![X12 : $i, X13 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.43/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.69  thf('40', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.43/0.69  thf('41', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('42', plain,
% 0.43/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.43/0.69           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.69  thf('43', plain,
% 0.43/0.69      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.69         = (k5_xboole_0 @ sk_B @ 
% 0.43/0.69            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.43/0.69             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.43/0.69      inference('demod', [status(thm)], ['36', '37', '40', '41', '42'])).
% 0.43/0.69  thf('44', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf(t92_xboole_1, axiom,
% 0.43/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.69  thf('45', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.69  thf('46', plain,
% 0.43/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.43/0.69           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.69  thf('47', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['45', '46'])).
% 0.43/0.69  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.69  thf('49', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('demod', [status(thm)], ['47', '48'])).
% 0.43/0.69  thf('50', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['44', '49'])).
% 0.43/0.69  thf('51', plain,
% 0.43/0.69      (((sk_B)
% 0.43/0.69         = (k5_xboole_0 @ 
% 0.43/0.69            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.43/0.69             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.43/0.69            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.43/0.69             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.43/0.69      inference('sup+', [status(thm)], ['43', '50'])).
% 0.43/0.69  thf('52', plain,
% 0.43/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.43/0.69           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.69  thf('53', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.43/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.69  thf('54', plain,
% 0.43/0.69      (![X12 : $i, X13 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ X12 @ X13)
% 0.43/0.69           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.43/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.69  thf('55', plain,
% 0.43/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.43/0.69  thf('56', plain,
% 0.43/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.43/0.69  thf('57', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.69  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['56', '57'])).
% 0.43/0.69  thf('59', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.69  thf('61', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.43/0.69      inference('demod', [status(thm)], ['51', '52', '55', '58', '59', '60'])).
% 0.43/0.69  thf('62', plain,
% 0.43/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.43/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.69  thf(t28_xboole_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.69  thf('63', plain,
% 0.43/0.69      (![X14 : $i, X15 : $i]:
% 0.43/0.69         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.43/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.69  thf('64', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.43/0.69           = (k4_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.43/0.69  thf('65', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.69  thf('66', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.43/0.69           = (k4_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.43/0.69  thf('67', plain,
% 0.43/0.69      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.43/0.69         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.43/0.69      inference('sup+', [status(thm)], ['61', '66'])).
% 0.43/0.69  thf('68', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.69  thf('69', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.43/0.69      inference('demod', [status(thm)], ['51', '52', '55', '58', '59', '60'])).
% 0.43/0.69  thf('70', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.43/0.69      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.43/0.69  thf('71', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.43/0.69  thf('72', plain,
% 0.43/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.43/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.43/0.69      inference('sup+', [status(thm)], ['70', '71'])).
% 0.43/0.69  thf('73', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.43/0.69      inference('demod', [status(thm)], ['51', '52', '55', '58', '59', '60'])).
% 0.43/0.69  thf('74', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.43/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.43/0.69  thf('75', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.43/0.69      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.43/0.69  thf('76', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.69      inference('demod', [status(thm)], ['47', '48'])).
% 0.43/0.69  thf('77', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.43/0.69      inference('sup+', [status(thm)], ['75', '76'])).
% 0.43/0.69  thf('78', plain,
% 0.43/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.43/0.69  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['56', '57'])).
% 0.43/0.69  thf('80', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.43/0.69  thf('81', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.43/0.69  thf(t69_enumset1, axiom,
% 0.43/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.69  thf('82', plain,
% 0.43/0.69      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.43/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.69  thf(l51_zfmisc_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.69  thf('83', plain,
% 0.43/0.69      (![X58 : $i, X59 : $i]:
% 0.43/0.69         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.43/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.69  thf('84', plain,
% 0.43/0.69      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['82', '83'])).
% 0.43/0.69  thf('85', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.43/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.69  thf('86', plain,
% 0.43/0.69      (![X23 : $i, X24 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.43/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.43/0.69              (k5_xboole_0 @ X23 @ X24)))),
% 0.43/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.69  thf('87', plain,
% 0.43/0.69      (![X0 : $i]:
% 0.43/0.69         ((k2_xboole_0 @ X0 @ X0)
% 0.43/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['85', '86'])).
% 0.43/0.69  thf('88', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.69  thf('89', plain,
% 0.43/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['87', '88'])).
% 0.43/0.69  thf('90', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.43/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.69  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.69      inference('demod', [status(thm)], ['89', '90'])).
% 0.43/0.69  thf('92', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.43/0.69      inference('demod', [status(thm)], ['84', '91'])).
% 0.43/0.69  thf('93', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.43/0.69      inference('sup+', [status(thm)], ['81', '92'])).
% 0.43/0.69  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.43/0.69  thf('94', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.69      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.43/0.69  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['93', '94'])).
% 0.43/0.69  thf('96', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['80', '95'])).
% 0.43/0.69  thf('97', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.69      inference('demod', [status(thm)], ['80', '95'])).
% 0.43/0.69  thf('98', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.69      inference('sup+', [status(thm)], ['56', '57'])).
% 0.43/0.69  thf('99', plain,
% 0.43/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.43/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.69  thf('100', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.43/0.69      inference('sup+', [status(thm)], ['98', '99'])).
% 0.43/0.69  thf('101', plain,
% 0.43/0.69      (![X14 : $i, X15 : $i]:
% 0.43/0.69         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.43/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.69  thf('102', plain,
% 0.43/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['100', '101'])).
% 0.43/0.69  thf(d7_xboole_0, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.43/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.69  thf('103', plain,
% 0.43/0.69      (![X4 : $i, X6 : $i]:
% 0.43/0.69         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.43/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.69  thf('104', plain,
% 0.43/0.69      (![X0 : $i]:
% 0.43/0.69         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['102', '103'])).
% 0.43/0.69  thf('105', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.43/0.69      inference('simplify', [status(thm)], ['104'])).
% 0.43/0.69  thf('106', plain, ($false),
% 0.43/0.69      inference('demod', [status(thm)], ['17', '96', '97', '105'])).
% 0.43/0.69  
% 0.43/0.69  % SZS output end Refutation
% 0.43/0.69  
% 0.43/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
