%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zjEko9tJqu

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:04 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 154 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  548 (1009 expanded)
%              Number of equality atoms :   56 (  87 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X59: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X59 ) @ ( k1_zfmisc_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X58: $i] :
      ( ( k2_subset_1 @ X58 )
      = X58 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X59: $i] :
      ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X59 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) )
      | ( ( k4_subset_1 @ X62 @ X61 @ X63 )
        = ( k2_xboole_0 @ X61 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ X56 )
      | ( r2_hidden @ X55 @ X56 )
      | ( v1_xboole_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X60: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X54: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['23','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','48'])).

thf('50',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X58: $i] :
      ( ( k2_subset_1 @ X58 )
      = X58 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X58: $i] :
      ( ( k2_subset_1 @ X58 )
      = X58 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('53',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zjEko9tJqu
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 210 iterations in 0.086s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(dt_k2_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X59 : $i]: (m1_subset_1 @ (k2_subset_1 @ X59) @ (k1_zfmisc_1 @ X59))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.54  thf('1', plain, (![X58 : $i]: ((k2_subset_1 @ X58) = (X58))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('2', plain, (![X59 : $i]: (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X59))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(t28_subset_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.36/0.54  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 0.36/0.54          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62))
% 0.36/0.54          | ((k4_subset_1 @ X62 @ X61 @ X63) = (k2_xboole_0 @ X61 @ X63)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.36/0.54  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d2_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X55 : $i, X56 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X55 @ X56)
% 0.36/0.54          | (r2_hidden @ X55 @ X56)
% 0.36/0.54          | (v1_xboole_0 @ X56))),
% 0.36/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf(fc1_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.54  thf('10', plain, (![X60 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X60))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.54  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf(l49_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X50 : $i, X51 : $i]:
% 0.36/0.54         ((r1_tarski @ X50 @ (k3_tarski @ X51)) | ~ (r2_hidden @ X50 @ X51))),
% 0.36/0.54      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.36/0.54  thf('13', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf(t99_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.36/0.54  thf('14', plain, (![X54 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X54)) = (X54))),
% 0.36/0.54      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.36/0.54  thf('15', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf(t28_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.54  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf(t94_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k2_xboole_0 @ A @ B ) =
% 0.36/0.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X21 @ X22)
% 0.36/0.54           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.36/0.54              (k3_xboole_0 @ X21 @ X22)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.36/0.54  thf(t91_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.36/0.54           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X21 @ X22)
% 0.36/0.54           = (k5_xboole_0 @ X21 @ 
% 0.36/0.54              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.36/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['17', '20'])).
% 0.36/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.36/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf(t100_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.54  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf(t112_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.36/0.54       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.36/0.54           = (k3_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))
% 0.36/0.54           = (k3_xboole_0 @ (k5_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))
% 0.36/0.54           = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (((k4_xboole_0 @ sk_B @ sk_A)
% 0.36/0.54         = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['27', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf(t79_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.36/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.36/0.54  thf(d7_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.36/0.54  thf('41', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['26', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.36/0.54           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.54           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.54  thf(t5_boole, axiom,
% 0.36/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.54  thf('45', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.54  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X0 : $i]: ((X0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['43', '46'])).
% 0.36/0.54  thf('48', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '47'])).
% 0.36/0.54  thf('49', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '48'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.36/0.54         != (k2_subset_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('51', plain, (![X58 : $i]: ((k2_subset_1 @ X58) = (X58))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('52', plain, (![X58 : $i]: ((k2_subset_1 @ X58) = (X58))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('53', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.36/0.54  thf('54', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['49', '53'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
