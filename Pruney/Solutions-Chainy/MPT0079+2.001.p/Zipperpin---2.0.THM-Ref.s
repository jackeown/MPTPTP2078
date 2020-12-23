%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rqhGxTFxbs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:56 EST 2020

% Result     : Theorem 12.70s
% Output     : Refutation 12.70s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 695 expanded)
%              Number of leaves         :   25 ( 234 expanded)
%              Depth                    :   23
%              Number of atoms          : 1110 (4895 expanded)
%              Number of equality atoms :  126 ( 643 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ sk_D @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','45'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('59',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference('sup+',[status(thm)],['52','69'])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['51','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('79',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('82',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('90',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf('95',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','97'])).

thf('99',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['0','98'])).

thf('100',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('101',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_D @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ sk_D )
      = ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('108',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('110',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_D ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['93','96'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('117',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('119',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X30 @ X32 )
      | ~ ( r1_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','121'])).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('124',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('127',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('128',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('129',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('131',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('135',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('137',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('139',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['124','125','126','139'])).

thf('141',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['140','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rqhGxTFxbs
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 12.70/12.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.70/12.88  % Solved by: fo/fo7.sh
% 12.70/12.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.70/12.88  % done 16055 iterations in 12.415s
% 12.70/12.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.70/12.88  % SZS output start Refutation
% 12.70/12.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.70/12.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.70/12.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.70/12.88  thf(sk_D_type, type, sk_D: $i).
% 12.70/12.88  thf(sk_C_type, type, sk_C: $i).
% 12.70/12.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.70/12.88  thf(sk_B_type, type, sk_B: $i).
% 12.70/12.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.70/12.88  thf(sk_A_type, type, sk_A: $i).
% 12.70/12.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.70/12.88  thf(t7_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 12.70/12.88  thf('0', plain,
% 12.70/12.88      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 12.70/12.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.70/12.88  thf(t72_xboole_1, conjecture,
% 12.70/12.88    (![A:$i,B:$i,C:$i,D:$i]:
% 12.70/12.88     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 12.70/12.88         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 12.70/12.88       ( ( C ) = ( B ) ) ))).
% 12.70/12.88  thf(zf_stmt_0, negated_conjecture,
% 12.70/12.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 12.70/12.88        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 12.70/12.88            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 12.70/12.88          ( ( C ) = ( B ) ) ) )),
% 12.70/12.88    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 12.70/12.88  thf('1', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.70/12.88  thf(commutativity_k2_xboole_0, axiom,
% 12.70/12.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 12.70/12.88  thf('2', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf('3', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['1', '2'])).
% 12.70/12.88  thf(t39_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.70/12.88  thf('4', plain,
% 12.70/12.88      (![X16 : $i, X17 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 12.70/12.88           = (k2_xboole_0 @ X16 @ X17))),
% 12.70/12.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.70/12.88  thf(t43_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i,C:$i]:
% 12.70/12.88     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 12.70/12.88       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 12.70/12.88  thf('5', plain,
% 12.70/12.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.70/12.88         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.70/12.88          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.70/12.88      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.70/12.88  thf('6', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.70/12.88         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 12.70/12.88          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 12.70/12.88      inference('sup-', [status(thm)], ['4', '5'])).
% 12.70/12.88  thf('7', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 12.70/12.88          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 12.70/12.88             (k4_xboole_0 @ sk_D @ sk_C)))),
% 12.70/12.88      inference('sup-', [status(thm)], ['3', '6'])).
% 12.70/12.88  thf('8', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['1', '2'])).
% 12.70/12.88  thf('9', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf('10', plain,
% 12.70/12.88      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 12.70/12.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.70/12.88  thf('11', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['9', '10'])).
% 12.70/12.88  thf('12', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 12.70/12.88      inference('sup+', [status(thm)], ['8', '11'])).
% 12.70/12.88  thf('13', plain,
% 12.70/12.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.70/12.88         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.70/12.88          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.70/12.88      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.70/12.88  thf('14', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 12.70/12.88      inference('sup-', [status(thm)], ['12', '13'])).
% 12.70/12.88  thf(t12_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 12.70/12.88  thf('15', plain,
% 12.70/12.88      (![X8 : $i, X9 : $i]:
% 12.70/12.88         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.70/12.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.70/12.88  thf('16', plain,
% 12.70/12.88      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (sk_A))),
% 12.70/12.88      inference('sup-', [status(thm)], ['14', '15'])).
% 12.70/12.88  thf('17', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf('18', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 12.70/12.88      inference('demod', [status(thm)], ['16', '17'])).
% 12.70/12.88  thf('19', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf(t46_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 12.70/12.88  thf('20', plain,
% 12.70/12.88      (![X21 : $i, X22 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 12.70/12.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 12.70/12.88  thf('21', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['19', '20'])).
% 12.70/12.88  thf('22', plain,
% 12.70/12.88      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (k1_xboole_0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['18', '21'])).
% 12.70/12.88  thf('23', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 12.70/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.70/12.88  thf(d7_xboole_0, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( r1_xboole_0 @ A @ B ) <=>
% 12.70/12.88       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 12.70/12.88  thf('24', plain,
% 12.70/12.88      (![X4 : $i, X5 : $i]:
% 12.70/12.88         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 12.70/12.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.70/12.88  thf('25', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 12.70/12.88      inference('sup-', [status(thm)], ['23', '24'])).
% 12.70/12.88  thf(commutativity_k3_xboole_0, axiom,
% 12.70/12.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 12.70/12.88  thf('26', plain,
% 12.70/12.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.70/12.88  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 12.70/12.88      inference('demod', [status(thm)], ['25', '26'])).
% 12.70/12.88  thf('28', plain,
% 12.70/12.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.70/12.88  thf(t47_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.70/12.88  thf('29', plain,
% 12.70/12.88      (![X23 : $i, X24 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 12.70/12.88           = (k4_xboole_0 @ X23 @ X24))),
% 12.70/12.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 12.70/12.88  thf('30', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.70/12.88           = (k4_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('sup+', [status(thm)], ['28', '29'])).
% 12.70/12.88  thf('31', plain,
% 12.70/12.88      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 12.70/12.88      inference('sup+', [status(thm)], ['27', '30'])).
% 12.70/12.88  thf(idempotence_k2_xboole_0, axiom,
% 12.70/12.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 12.70/12.88  thf('32', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 12.70/12.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 12.70/12.88  thf('33', plain,
% 12.70/12.88      (![X21 : $i, X22 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 12.70/12.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 12.70/12.88  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['32', '33'])).
% 12.70/12.88  thf('35', plain,
% 12.70/12.88      (![X16 : $i, X17 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 12.70/12.88           = (k2_xboole_0 @ X16 @ X17))),
% 12.70/12.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.70/12.88  thf('36', plain,
% 12.70/12.88      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['34', '35'])).
% 12.70/12.88  thf('37', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 12.70/12.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 12.70/12.88  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('demod', [status(thm)], ['36', '37'])).
% 12.70/12.88  thf('39', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['38', '39'])).
% 12.70/12.88  thf('41', plain,
% 12.70/12.88      (![X16 : $i, X17 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 12.70/12.88           = (k2_xboole_0 @ X16 @ X17))),
% 12.70/12.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.70/12.88  thf('42', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['40', '41'])).
% 12.70/12.88  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['38', '39'])).
% 12.70/12.88  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.70/12.88  thf('45', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 12.70/12.88      inference('demod', [status(thm)], ['31', '44'])).
% 12.70/12.88  thf('46', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 12.70/12.88      inference('demod', [status(thm)], ['22', '45'])).
% 12.70/12.88  thf(t48_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i]:
% 12.70/12.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.70/12.88  thf('47', plain,
% 12.70/12.88      (![X25 : $i, X26 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 12.70/12.88           = (k3_xboole_0 @ X25 @ X26))),
% 12.70/12.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.70/12.88  thf('48', plain,
% 12.70/12.88      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_A))),
% 12.70/12.88      inference('sup+', [status(thm)], ['46', '47'])).
% 12.70/12.88  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.70/12.88  thf('50', plain,
% 12.70/12.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.70/12.88  thf('51', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['48', '49', '50'])).
% 12.70/12.88  thf('52', plain,
% 12.70/12.88      (![X25 : $i, X26 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 12.70/12.88           = (k3_xboole_0 @ X25 @ X26))),
% 12.70/12.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.70/12.88  thf('53', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 12.70/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.70/12.88  thf('54', plain,
% 12.70/12.88      (![X4 : $i, X5 : $i]:
% 12.70/12.88         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 12.70/12.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.70/12.88  thf('55', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 12.70/12.88      inference('sup-', [status(thm)], ['53', '54'])).
% 12.70/12.88  thf('56', plain,
% 12.70/12.88      (![X23 : $i, X24 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 12.70/12.88           = (k4_xboole_0 @ X23 @ X24))),
% 12.70/12.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 12.70/12.88  thf('57', plain,
% 12.70/12.88      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 12.70/12.88      inference('sup+', [status(thm)], ['55', '56'])).
% 12.70/12.88  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.70/12.88  thf('59', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 12.70/12.88      inference('demod', [status(thm)], ['57', '58'])).
% 12.70/12.88  thf(t52_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i,C:$i]:
% 12.70/12.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 12.70/12.88       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 12.70/12.88  thf('60', plain,
% 12.70/12.88      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 12.70/12.88           = (k2_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 12.70/12.88              (k3_xboole_0 @ X27 @ X29)))),
% 12.70/12.88      inference('cnf', [status(esa)], [t52_xboole_1])).
% 12.70/12.88  thf('61', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 12.70/12.88           = (k2_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ X0)))),
% 12.70/12.88      inference('sup+', [status(thm)], ['59', '60'])).
% 12.70/12.88  thf('62', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 12.70/12.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 12.70/12.88  thf(t29_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i,C:$i]:
% 12.70/12.88     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 12.70/12.88  thf('63', plain,
% 12.70/12.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.70/12.88         (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ (k2_xboole_0 @ X10 @ X12))),
% 12.70/12.88      inference('cnf', [status(esa)], [t29_xboole_1])).
% 12.70/12.88  thf('64', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 12.70/12.88      inference('sup+', [status(thm)], ['62', '63'])).
% 12.70/12.88  thf('65', plain,
% 12.70/12.88      (![X8 : $i, X9 : $i]:
% 12.70/12.88         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.70/12.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.70/12.88  thf('66', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 12.70/12.88      inference('sup-', [status(thm)], ['64', '65'])).
% 12.70/12.88  thf('67', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.88  thf('68', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 12.70/12.88      inference('demod', [status(thm)], ['66', '67'])).
% 12.70/12.88  thf('69', plain,
% 12.70/12.88      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 12.70/12.88      inference('demod', [status(thm)], ['61', '68'])).
% 12.70/12.88  thf('70', plain,
% 12.70/12.88      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 12.70/12.88      inference('sup+', [status(thm)], ['52', '69'])).
% 12.70/12.88  thf('71', plain,
% 12.70/12.88      (![X25 : $i, X26 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 12.70/12.88           = (k3_xboole_0 @ X25 @ X26))),
% 12.70/12.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.70/12.88  thf('72', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ sk_C @ sk_C)
% 12.70/12.88           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))),
% 12.70/12.88      inference('sup+', [status(thm)], ['70', '71'])).
% 12.70/12.88  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['32', '33'])).
% 12.70/12.88  thf('74', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))),
% 12.70/12.88      inference('demod', [status(thm)], ['72', '73'])).
% 12.70/12.88  thf('75', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.88      inference('sup+', [status(thm)], ['51', '74'])).
% 12.70/12.88  thf('76', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.70/12.88           = (k4_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('sup+', [status(thm)], ['28', '29'])).
% 12.70/12.88  thf('77', plain,
% 12.70/12.88      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_C))),
% 12.70/12.88      inference('sup+', [status(thm)], ['75', '76'])).
% 12.70/12.88  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.70/12.88  thf('79', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_C))),
% 12.70/12.88      inference('demod', [status(thm)], ['77', '78'])).
% 12.70/12.88  thf('80', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 12.70/12.88          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['7', '79'])).
% 12.70/12.88  thf('81', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['9', '10'])).
% 12.70/12.88  thf('82', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['1', '2'])).
% 12.70/12.88  thf('83', plain,
% 12.70/12.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.70/12.88         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.70/12.88          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.70/12.88      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.70/12.88  thf('84', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 12.70/12.88          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 12.70/12.88      inference('sup-', [status(thm)], ['82', '83'])).
% 12.70/12.88  thf('85', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D)),
% 12.70/12.88      inference('sup-', [status(thm)], ['81', '84'])).
% 12.70/12.88  thf('86', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 12.70/12.88      inference('sup-', [status(thm)], ['53', '54'])).
% 12.70/12.88  thf('87', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.70/12.88           = (k4_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('sup+', [status(thm)], ['28', '29'])).
% 12.70/12.88  thf('88', plain,
% 12.70/12.88      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 12.70/12.88      inference('sup+', [status(thm)], ['86', '87'])).
% 12.70/12.88  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.70/12.88  thf('90', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 12.70/12.88      inference('demod', [status(thm)], ['88', '89'])).
% 12.70/12.88  thf('91', plain, ((r1_tarski @ sk_A @ sk_D)),
% 12.70/12.88      inference('demod', [status(thm)], ['85', '90'])).
% 12.70/12.88  thf('92', plain,
% 12.70/12.88      (![X8 : $i, X9 : $i]:
% 12.70/12.88         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.70/12.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.70/12.88  thf('93', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 12.70/12.88      inference('sup-', [status(thm)], ['91', '92'])).
% 12.70/12.88  thf('94', plain,
% 12.70/12.88      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 12.70/12.88      inference('demod', [status(thm)], ['16', '17'])).
% 12.70/12.88  thf('95', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 12.70/12.88      inference('demod', [status(thm)], ['31', '44'])).
% 12.70/12.88  thf('96', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 12.70/12.88      inference('demod', [status(thm)], ['94', '95'])).
% 12.70/12.88  thf('97', plain, (((sk_D) = (sk_A))),
% 12.70/12.88      inference('sup+', [status(thm)], ['93', '96'])).
% 12.70/12.88  thf('98', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 12.70/12.88          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 12.70/12.88      inference('demod', [status(thm)], ['80', '97'])).
% 12.70/12.88  thf('99', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 12.70/12.88      inference('sup-', [status(thm)], ['0', '98'])).
% 12.70/12.88  thf('100', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 12.70/12.88      inference('demod', [status(thm)], ['31', '44'])).
% 12.70/12.88  thf('101', plain,
% 12.70/12.88      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 12.70/12.88           = (k2_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 12.70/12.88              (k3_xboole_0 @ X27 @ X29)))),
% 12.70/12.88      inference('cnf', [status(esa)], [t52_xboole_1])).
% 12.70/12.88  thf('102', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ X0))
% 12.70/12.88           = (k2_xboole_0 @ sk_D @ (k3_xboole_0 @ sk_D @ X0)))),
% 12.70/12.88      inference('sup+', [status(thm)], ['100', '101'])).
% 12.70/12.88  thf('103', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 12.70/12.88      inference('demod', [status(thm)], ['66', '67'])).
% 12.70/12.88  thf('104', plain,
% 12.70/12.88      (![X0 : $i]: ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ X0)) = (sk_D))),
% 12.70/12.88      inference('demod', [status(thm)], ['102', '103'])).
% 12.70/12.88  thf('105', plain,
% 12.70/12.88      (![X25 : $i, X26 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 12.70/12.88           = (k3_xboole_0 @ X25 @ X26))),
% 12.70/12.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.70/12.88  thf('106', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k4_xboole_0 @ sk_D @ sk_D)
% 12.70/12.88           = (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ X0)))),
% 12.70/12.88      inference('sup+', [status(thm)], ['104', '105'])).
% 12.70/12.88  thf('107', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.70/12.88      inference('sup+', [status(thm)], ['32', '33'])).
% 12.70/12.88  thf('108', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         ((k1_xboole_0) = (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ X0)))),
% 12.70/12.88      inference('demod', [status(thm)], ['106', '107'])).
% 12.70/12.88  thf('109', plain,
% 12.70/12.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.70/12.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.70/12.88  thf('110', plain,
% 12.70/12.88      (![X4 : $i, X6 : $i]:
% 12.70/12.88         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 12.70/12.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.70/12.88  thf('111', plain,
% 12.70/12.88      (![X0 : $i, X1 : $i]:
% 12.70/12.88         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 12.70/12.88      inference('sup-', [status(thm)], ['109', '110'])).
% 12.70/12.88  thf('112', plain,
% 12.70/12.88      (![X0 : $i]:
% 12.70/12.88         (((k1_xboole_0) != (k1_xboole_0))
% 12.70/12.88          | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_D))),
% 12.70/12.88      inference('sup-', [status(thm)], ['108', '111'])).
% 12.70/12.88  thf('113', plain,
% 12.70/12.88      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_D)),
% 12.70/12.88      inference('simplify', [status(thm)], ['112'])).
% 12.70/12.88  thf('114', plain, (((sk_D) = (sk_A))),
% 12.70/12.88      inference('sup+', [status(thm)], ['93', '96'])).
% 12.70/12.88  thf('115', plain,
% 12.70/12.88      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 12.70/12.88      inference('demod', [status(thm)], ['113', '114'])).
% 12.70/12.88  thf('116', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 12.70/12.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 12.70/12.88  thf('117', plain,
% 12.70/12.88      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 12.70/12.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.70/12.88  thf('118', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 12.70/12.88      inference('sup+', [status(thm)], ['116', '117'])).
% 12.70/12.88  thf(t67_xboole_1, axiom,
% 12.70/12.88    (![A:$i,B:$i,C:$i]:
% 12.70/12.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 12.70/12.88         ( r1_xboole_0 @ B @ C ) ) =>
% 12.70/12.88       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.70/12.88  thf('119', plain,
% 12.70/12.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 12.70/12.88         (((X30) = (k1_xboole_0))
% 12.70/12.89          | ~ (r1_tarski @ X30 @ X31)
% 12.70/12.89          | ~ (r1_tarski @ X30 @ X32)
% 12.70/12.89          | ~ (r1_xboole_0 @ X31 @ X32))),
% 12.70/12.89      inference('cnf', [status(esa)], [t67_xboole_1])).
% 12.70/12.89  thf('120', plain,
% 12.70/12.89      (![X0 : $i, X1 : $i]:
% 12.70/12.89         (~ (r1_xboole_0 @ X0 @ X1)
% 12.70/12.89          | ~ (r1_tarski @ X0 @ X1)
% 12.70/12.89          | ((X0) = (k1_xboole_0)))),
% 12.70/12.89      inference('sup-', [status(thm)], ['118', '119'])).
% 12.70/12.89  thf('121', plain,
% 12.70/12.89      (![X0 : $i]:
% 12.70/12.89         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 12.70/12.89          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 12.70/12.89      inference('sup-', [status(thm)], ['115', '120'])).
% 12.70/12.89  thf('122', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 12.70/12.89      inference('sup-', [status(thm)], ['99', '121'])).
% 12.70/12.89  thf('123', plain,
% 12.70/12.89      (![X16 : $i, X17 : $i]:
% 12.70/12.89         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 12.70/12.89           = (k2_xboole_0 @ X16 @ X17))),
% 12.70/12.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.70/12.89  thf('124', plain,
% 12.70/12.89      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B))),
% 12.70/12.89      inference('sup+', [status(thm)], ['122', '123'])).
% 12.70/12.89  thf('125', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.70/12.89      inference('demod', [status(thm)], ['36', '37'])).
% 12.70/12.89  thf('126', plain,
% 12.70/12.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.89  thf('127', plain,
% 12.70/12.89      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 12.70/12.89      inference('demod', [status(thm)], ['1', '2'])).
% 12.70/12.89  thf('128', plain,
% 12.70/12.89      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 12.70/12.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.70/12.89  thf('129', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))),
% 12.70/12.89      inference('sup+', [status(thm)], ['127', '128'])).
% 12.70/12.89  thf('130', plain,
% 12.70/12.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.89  thf('131', plain,
% 12.70/12.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.70/12.89         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.70/12.89          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.70/12.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.70/12.89  thf('132', plain,
% 12.70/12.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.70/12.89         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 12.70/12.89          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 12.70/12.89      inference('sup-', [status(thm)], ['130', '131'])).
% 12.70/12.89  thf('133', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 12.70/12.89      inference('sup-', [status(thm)], ['129', '132'])).
% 12.70/12.89  thf('134', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 12.70/12.89      inference('demod', [status(thm)], ['57', '58'])).
% 12.70/12.89  thf('135', plain, ((r1_tarski @ sk_C @ sk_B)),
% 12.70/12.89      inference('demod', [status(thm)], ['133', '134'])).
% 12.70/12.89  thf('136', plain,
% 12.70/12.89      (![X8 : $i, X9 : $i]:
% 12.70/12.89         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.70/12.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.70/12.89  thf('137', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 12.70/12.89      inference('sup-', [status(thm)], ['135', '136'])).
% 12.70/12.89  thf('138', plain,
% 12.70/12.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.70/12.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.70/12.89  thf('139', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 12.70/12.89      inference('demod', [status(thm)], ['137', '138'])).
% 12.70/12.89  thf('140', plain, (((sk_C) = (sk_B))),
% 12.70/12.89      inference('demod', [status(thm)], ['124', '125', '126', '139'])).
% 12.70/12.89  thf('141', plain, (((sk_C) != (sk_B))),
% 12.70/12.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.70/12.89  thf('142', plain, ($false),
% 12.70/12.89      inference('simplify_reflect-', [status(thm)], ['140', '141'])).
% 12.70/12.89  
% 12.70/12.89  % SZS output end Refutation
% 12.70/12.89  
% 12.70/12.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
