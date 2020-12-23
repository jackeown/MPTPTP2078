%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iEsIustQhh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:30 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 159 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   24
%              Number of atoms          :  600 (1084 expanded)
%              Number of equality atoms :   60 ( 103 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('65',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['63','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['60','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iEsIustQhh
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 380 iterations in 0.173s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(t106_xboole_1, conjecture,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.38/0.63       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.63        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.38/0.63          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.38/0.63  thf('0', plain,
% 0.38/0.63      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.63  thf(t46_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      (![X21 : $i, X22 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 0.38/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.63  thf(t36_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.38/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.63  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.63  thf(t28_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X17 : $i, X18 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.38/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.63  thf(t100_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      (![X10 : $i, X11 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X10 @ X11)
% 0.38/0.63           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.63  thf(t5_boole, axiom,
% 0.38/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.63  thf('12', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.63  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.63  thf('14', plain,
% 0.38/0.63      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.38/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.63  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.63  thf(l32_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.63  thf(t49_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.63       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.38/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.63  thf('19', plain,
% 0.38/0.63      (![X7 : $i, X8 : $i]:
% 0.38/0.63         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('21', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.38/0.63  thf('22', plain,
% 0.38/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.63  thf('23', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.63  thf('24', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.63  thf('25', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.63      inference('sup+', [status(thm)], ['2', '24'])).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.63  thf('28', plain,
% 0.38/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.38/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.38/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.63  thf('30', plain,
% 0.38/0.63      (![X10 : $i, X11 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X10 @ X11)
% 0.38/0.63           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.63           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.63  thf('32', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.63  thf('33', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['31', '32'])).
% 0.38/0.63  thf('34', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.63  thf('35', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.63  thf('38', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('39', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 0.38/0.63             (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.63  thf('40', plain,
% 0.38/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.63  thf('41', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 0.38/0.63             (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.63  thf('43', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.63      inference('sup+', [status(thm)], ['34', '42'])).
% 0.38/0.63  thf('44', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('45', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.38/0.63           (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.63  thf('46', plain,
% 0.38/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.38/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.63  thf('47', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ sk_A @ 
% 0.38/0.63           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 0.38/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.63  thf('48', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['33', '47'])).
% 0.38/0.63  thf('49', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.63  thf('50', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.38/0.63      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.63  thf('51', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.63  thf(d7_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.63  thf('52', plain,
% 0.38/0.63      (![X4 : $i, X6 : $i]:
% 0.38/0.63         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.63  thf('53', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.63  thf('54', plain,
% 0.38/0.63      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['50', '53'])).
% 0.38/0.63  thf('55', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.38/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.38/0.63  thf('56', plain,
% 0.38/0.63      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('57', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.63  thf('58', plain,
% 0.38/0.63      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('59', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.38/0.63  thf('60', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.38/0.63  thf('61', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('62', plain,
% 0.38/0.63      (![X17 : $i, X18 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.38/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.63  thf('63', plain,
% 0.38/0.63      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.63  thf('64', plain,
% 0.38/0.63      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.38/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.63  thf('65', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('66', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.63  thf('67', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('68', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.63  thf('69', plain,
% 0.38/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.63  thf('70', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['68', '69'])).
% 0.38/0.63  thf('71', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0)),
% 0.38/0.63      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.63  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.63      inference('sup+', [status(thm)], ['63', '71'])).
% 0.38/0.63  thf('73', plain, ($false), inference('demod', [status(thm)], ['60', '72'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
