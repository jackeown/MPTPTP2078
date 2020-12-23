%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1lNx0uLDM

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:34 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 289 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   24
%              Number of atoms          :  809 (2008 expanded)
%              Number of equality atoms :   91 ( 230 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('50',plain,(
    ! [X0: $i] :
      ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['26','71'])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['72','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1lNx0uLDM
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.15  % Solved by: fo/fo7.sh
% 0.89/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.15  % done 1182 iterations in 0.689s
% 0.89/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.15  % SZS output start Refutation
% 0.89/1.15  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.89/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.15  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.89/1.15  thf(t63_xboole_1, conjecture,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.89/1.15       ( r1_xboole_0 @ A @ C ) ))).
% 0.89/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.15    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.15        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.89/1.15          ( r1_xboole_0 @ A @ C ) ) )),
% 0.89/1.15    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.89/1.15  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf(t3_boole, axiom,
% 0.89/1.15    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.15  thf('1', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.89/1.15      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.15  thf(t48_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('2', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('3', plain,
% 0.89/1.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['1', '2'])).
% 0.89/1.15  thf(t36_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.15  thf('4', plain,
% 0.89/1.15      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.89/1.15      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.15  thf(t12_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.89/1.15  thf('5', plain,
% 0.89/1.15      (![X14 : $i, X15 : $i]:
% 0.89/1.15         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.89/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.15  thf('6', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.15  thf(commutativity_k2_xboole_0, axiom,
% 0.89/1.15    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.89/1.15  thf('7', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('8', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.89/1.15      inference('demod', [status(thm)], ['6', '7'])).
% 0.89/1.15  thf('9', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf(t1_boole, axiom,
% 0.89/1.15    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.15  thf('10', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.89/1.15      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.15  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['9', '10'])).
% 0.89/1.15  thf('12', plain,
% 0.89/1.15      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['8', '11'])).
% 0.89/1.15  thf('13', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('14', plain,
% 0.89/1.15      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['12', '13'])).
% 0.89/1.15  thf(d7_xboole_0, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.89/1.15       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.15  thf('15', plain,
% 0.89/1.15      (![X5 : $i, X7 : $i]:
% 0.89/1.15         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 0.89/1.15      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.15  thf('16', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.15  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.89/1.15      inference('simplify', [status(thm)], ['16'])).
% 0.89/1.15  thf(symmetry_r1_xboole_0, axiom,
% 0.89/1.15    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.89/1.15  thf('18', plain,
% 0.89/1.15      (![X8 : $i, X9 : $i]:
% 0.89/1.15         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.89/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.89/1.15  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.89/1.15      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.15  thf('20', plain,
% 0.89/1.15      (![X5 : $i, X6 : $i]:
% 0.89/1.15         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.89/1.15      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.15  thf('21', plain,
% 0.89/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.15  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['3', '21'])).
% 0.89/1.15  thf('23', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('24', plain,
% 0.89/1.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['22', '23'])).
% 0.89/1.15  thf('25', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.89/1.15      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.15  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.89/1.15      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.15  thf('27', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('28', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf('29', plain,
% 0.89/1.15      (![X14 : $i, X15 : $i]:
% 0.89/1.15         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.89/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.15  thf('30', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.89/1.15      inference('sup-', [status(thm)], ['28', '29'])).
% 0.89/1.15  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['3', '21'])).
% 0.89/1.15  thf(t41_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.89/1.15       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.89/1.15  thf('32', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('33', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['31', '32'])).
% 0.89/1.15  thf('34', plain,
% 0.89/1.15      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['8', '11'])).
% 0.89/1.15  thf('35', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['33', '34'])).
% 0.89/1.15  thf('36', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['30', '35'])).
% 0.89/1.15  thf('37', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('38', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.89/1.15           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['36', '37'])).
% 0.89/1.15  thf('39', plain,
% 0.89/1.15      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['8', '11'])).
% 0.89/1.15  thf('40', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.15  thf('41', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['27', '40'])).
% 0.89/1.15  thf('42', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('43', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('44', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.15  thf('45', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1) = (k1_xboole_0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['41', '44'])).
% 0.89/1.15  thf(t39_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('46', plain,
% 0.89/1.15      (![X19 : $i, X20 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.89/1.15           = (k2_xboole_0 @ X19 @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('47', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.89/1.15           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['45', '46'])).
% 0.89/1.15  thf('48', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['9', '10'])).
% 0.89/1.15  thf('50', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.89/1.15  thf('51', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf('52', plain,
% 0.89/1.15      (![X8 : $i, X9 : $i]:
% 0.89/1.15         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.89/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.89/1.15  thf('53', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.89/1.15      inference('sup-', [status(thm)], ['51', '52'])).
% 0.89/1.15  thf('54', plain,
% 0.89/1.15      (![X5 : $i, X6 : $i]:
% 0.89/1.15         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.89/1.15      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.15  thf('55', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['53', '54'])).
% 0.89/1.15  thf('56', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('57', plain,
% 0.89/1.15      (![X19 : $i, X20 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.89/1.15           = (k2_xboole_0 @ X19 @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('58', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['56', '57'])).
% 0.89/1.15  thf('59', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('60', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('61', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.89/1.15  thf('62', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.89/1.15      inference('demod', [status(thm)], ['6', '7'])).
% 0.89/1.15  thf('63', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (X1))),
% 0.89/1.15      inference('demod', [status(thm)], ['61', '62'])).
% 0.89/1.15  thf('64', plain,
% 0.89/1.15      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.89/1.15         = (sk_C_1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['55', '63'])).
% 0.89/1.15  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['9', '10'])).
% 0.89/1.15  thf('66', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.89/1.15      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.15  thf('67', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('68', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.89/1.15           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['66', '67'])).
% 0.89/1.15  thf('69', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0))
% 0.89/1.15           = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['50', '68'])).
% 0.89/1.15  thf('70', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.89/1.15      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.15  thf('71', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C_1))),
% 0.89/1.15      inference('demod', [status(thm)], ['69', '70'])).
% 0.89/1.15  thf('72', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['26', '71'])).
% 0.89/1.15  thf('73', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('74', plain,
% 0.89/1.15      (![X19 : $i, X20 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.89/1.15           = (k2_xboole_0 @ X19 @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('75', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.89/1.15           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['73', '74'])).
% 0.89/1.15  thf('76', plain,
% 0.89/1.15      (![X25 : $i, X26 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.89/1.15           = (k3_xboole_0 @ X25 @ X26))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('77', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('78', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.89/1.15           = (k4_xboole_0 @ X2 @ 
% 0.89/1.15              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.89/1.15      inference('sup+', [status(thm)], ['76', '77'])).
% 0.89/1.15  thf('79', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('80', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.89/1.15           = (k4_xboole_0 @ X2 @ 
% 0.89/1.15              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.89/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.89/1.15  thf('81', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.89/1.15      inference('sup+', [status(thm)], ['75', '80'])).
% 0.89/1.15  thf('82', plain,
% 0.89/1.15      (![X19 : $i, X20 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.89/1.15           = (k2_xboole_0 @ X19 @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('83', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.89/1.15      inference('demod', [status(thm)], ['81', '82'])).
% 0.89/1.15  thf('84', plain,
% 0.89/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.89/1.15           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.15  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['3', '21'])).
% 0.89/1.15  thf('86', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.89/1.15           = (k1_xboole_0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['84', '85'])).
% 0.89/1.15  thf('87', plain,
% 0.89/1.15      (![X19 : $i, X20 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.89/1.15           = (k2_xboole_0 @ X19 @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('88', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['86', '87'])).
% 0.89/1.15  thf('89', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['83', '88'])).
% 0.89/1.15  thf('90', plain,
% 0.89/1.15      (![X5 : $i, X7 : $i]:
% 0.89/1.15         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 0.89/1.15      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.15  thf('91', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         (((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.15          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['89', '90'])).
% 0.89/1.15  thf('92', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.89/1.15      inference('simplify', [status(thm)], ['91'])).
% 0.89/1.15  thf('93', plain,
% 0.89/1.15      (![X8 : $i, X9 : $i]:
% 0.89/1.15         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.89/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.89/1.15  thf('94', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['92', '93'])).
% 0.89/1.15  thf('95', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.89/1.15      inference('sup+', [status(thm)], ['72', '94'])).
% 0.89/1.15  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.89/1.15  
% 0.89/1.15  % SZS output end Refutation
% 0.89/1.15  
% 0.89/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
