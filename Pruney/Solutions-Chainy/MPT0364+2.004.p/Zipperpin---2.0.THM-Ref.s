%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1xtfWzAjZF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 126 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (1042 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X79: $i,X80: $i] :
      ( ( ( k3_subset_1 @ X79 @ X80 )
        = ( k4_xboole_0 @ X79 @ X80 ) )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ X36 @ X37 )
      | ( r1_xboole_0 @ X36 @ ( k4_xboole_0 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( r1_xboole_0 @ X34 @ ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X76 @ X77 )
      | ( r2_hidden @ X76 @ X77 )
      | ( v1_xboole_0 @ X77 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X81: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X72 @ X71 )
      | ( r1_tarski @ X72 @ X70 )
      | ( X71
       != ( k1_zfmisc_1 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X70: $i,X72: $i] :
      ( ( r1_tarski @ X72 @ X70 )
      | ~ ( r2_hidden @ X72 @ ( k1_zfmisc_1 @ X70 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(demod,[status(thm)],['37','38','39','42'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['14','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1xtfWzAjZF
% 0.14/0.37  % Computer   : n018.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:30:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 380 iterations in 0.144s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(t44_subset_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.45/0.63             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i]:
% 0.45/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63          ( ![C:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.45/0.63                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.45/0.63        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.45/0.63       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d5_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X79 : $i, X80 : $i]:
% 0.45/0.63         (((k3_subset_1 @ X79 @ X80) = (k4_xboole_0 @ X79 @ X80))
% 0.45/0.63          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ X79)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (((r1_tarski @ sk_B @ sk_C_1)
% 0.45/0.63        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf(t85_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X36 @ X37)
% 0.45/0.63          | (r1_xboole_0 @ X36 @ (k4_xboole_0 @ X38 @ X37)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.45/0.63         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.45/0.63         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['5', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.45/0.63         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.45/0.63       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.45/0.63  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.45/0.63         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.45/0.63       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.45/0.63  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(t81_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.45/0.63       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.63         ((r1_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X35))
% 0.45/0.63          | ~ (r1_xboole_0 @ X34 @ (k4_xboole_0 @ X33 @ X35)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.45/0.63          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.63  thf('22', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '21'])).
% 0.45/0.63  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d2_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X76 : $i, X77 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X76 @ X77)
% 0.45/0.63          | (r2_hidden @ X76 @ X77)
% 0.45/0.63          | (v1_xboole_0 @ X77))),
% 0.45/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.63  thf(fc1_subset_1, axiom,
% 0.45/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.63  thf('26', plain, (![X81 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X81))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.63  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.45/0.63  thf(d1_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X72 @ X71)
% 0.45/0.63          | (r1_tarski @ X72 @ X70)
% 0.45/0.63          | ((X71) != (k1_zfmisc_1 @ X70)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X70 : $i, X72 : $i]:
% 0.45/0.63         ((r1_tarski @ X72 @ X70) | ~ (r2_hidden @ X72 @ (k1_zfmisc_1 @ X70)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.63  thf('30', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.63  thf(t63_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.45/0.63       ( r1_xboole_0 @ A @ C ) ))).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X30 @ X31)
% 0.45/0.63          | ~ (r1_xboole_0 @ X31 @ X32)
% 0.45/0.63          | (r1_xboole_0 @ X30 @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '32'])).
% 0.45/0.63  thf(d7_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.63  thf(t100_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.45/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.45/0.63         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.63  thf(t48_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.45/0.63           = (k3_xboole_0 @ X24 @ X25))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf(commutativity_k5_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.63  thf(t5_boole, axiom,
% 0.45/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.63  thf('41', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 0.45/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.63  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['40', '41'])).
% 0.45/0.63  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '38', '39', '42'])).
% 0.45/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.63  thf(t17_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.63      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.63  thf('47', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.45/0.63      inference('sup+', [status(thm)], ['43', '46'])).
% 0.45/0.63  thf('48', plain, ($false), inference('demod', [status(thm)], ['14', '47'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
