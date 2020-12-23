%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H2wmdiX96i

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:59 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 107 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  487 ( 648 expanded)
%              Number of equality atoms :   56 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X27 ) @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','32'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','41'])).

thf('43',plain,(
    ( k5_xboole_0 @ sk_A @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H2wmdiX96i
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:03:34 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 103 iterations in 0.037s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.24/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.24/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(t28_subset_1, conjecture,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i]:
% 0.24/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.24/0.52         != (k2_subset_1 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.24/0.52  thf('1', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.52  thf('2', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.52  thf('3', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.24/0.52  thf(dt_k2_subset_1, axiom,
% 0.24/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (![X27 : $i]: (m1_subset_1 @ (k2_subset_1 @ X27) @ (k1_zfmisc_1 @ X27))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.24/0.52  thf('5', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.52  thf('6', plain, (![X27 : $i]: (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X27))),
% 0.24/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.52  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.24/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.24/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 0.24/0.52          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.24/0.52  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d2_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.24/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.24/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X23 : $i, X24 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X23 @ X24)
% 0.24/0.52          | (r2_hidden @ X23 @ X24)
% 0.24/0.52          | (v1_xboole_0 @ X24))),
% 0.24/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.24/0.52        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.52  thf(fc1_subset_1, axiom,
% 0.24/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.52  thf('14', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.24/0.52  thf('15', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf(d1_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X19 @ X18)
% 0.24/0.52          | (r1_tarski @ X19 @ X17)
% 0.24/0.52          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (![X17 : $i, X19 : $i]:
% 0.24/0.52         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.24/0.52  thf('18', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.52  thf(t28_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X6 : $i, X7 : $i]:
% 0.24/0.52         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.24/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.52  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.24/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.52  thf(t100_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      (![X3 : $i, X4 : $i]:
% 0.24/0.52         ((k4_xboole_0 @ X3 @ X4)
% 0.24/0.52           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.24/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf(d10_xboole_0, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.52  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (![X6 : $i, X7 : $i]:
% 0.24/0.52         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.24/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.52  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X3 : $i, X4 : $i]:
% 0.24/0.52         ((k4_xboole_0 @ X3 @ X4)
% 0.24/0.52           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.24/0.52  thf(t1_boole, axiom,
% 0.24/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.52  thf('29', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.52  thf(t46_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i]:
% 0.24/0.52         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.52  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.24/0.52  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['28', '31'])).
% 0.24/0.52  thf('33', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['22', '32'])).
% 0.24/0.52  thf(t98_xboole_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         ((k2_xboole_0 @ X10 @ X11)
% 0.24/0.52           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      (((k2_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.24/0.52  thf(commutativity_k2_tarski, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.24/0.52  thf('36', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.24/0.52  thf(l51_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      (![X21 : $i, X22 : $i]:
% 0.24/0.52         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.24/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.24/0.52  thf('38', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.52      inference('sup+', [status(thm)], ['36', '37'])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (![X21 : $i, X22 : $i]:
% 0.24/0.52         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.24/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['35', '40'])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '41'])).
% 0.24/0.52  thf('43', plain, (((k5_xboole_0 @ sk_A @ k1_xboole_0) != (sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['3', '42'])).
% 0.24/0.52  thf('44', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.52  thf('45', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.52  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['44', '45'])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i]:
% 0.24/0.52         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.52  thf('48', plain,
% 0.24/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         ((k2_xboole_0 @ X10 @ X11)
% 0.24/0.52           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.24/0.52  thf('51', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.52  thf('52', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['50', '51'])).
% 0.24/0.52  thf('53', plain, (((sk_A) != (sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['43', '52'])).
% 0.24/0.52  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
