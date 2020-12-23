%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArgncfpgEW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:04 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  522 (1310 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['14','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('35',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['16'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('41',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','23','44'])).

thf('46',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['26','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArgncfpgEW
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 305 iterations in 0.162s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(t44_subset_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.43/0.62             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62          ( ![C:$i]:
% 0.43/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.43/0.62                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.43/0.62  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d5_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i]:
% 0.43/0.62         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.43/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i]:
% 0.43/0.62         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.43/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf(t31_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62           ( ( r1_tarski @ B @ C ) <=>
% 0.43/0.62             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.43/0.62          | ~ (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ 
% 0.43/0.62               (k3_subset_1 @ X22 @ X23))
% 0.43/0.62          | (r1_tarski @ X23 @ X21)
% 0.43/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62             (k3_subset_1 @ sk_A @ X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.62          | (r1_tarski @ X0 @ sk_C_1)
% 0.43/0.62          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62             (k3_subset_1 @ sk_A @ X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.62          | (r1_tarski @ X0 @ sk_C_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62           (k4_xboole_0 @ sk_A @ sk_B))
% 0.43/0.62        | (r1_tarski @ sk_B @ sk_C_1)
% 0.43/0.62        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '9'])).
% 0.43/0.62  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62           (k4_xboole_0 @ sk_A @ sk_B))
% 0.43/0.62        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.43/0.62        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.43/0.62      inference('split', [status(esa)], ['13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.43/0.62       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.43/0.62      inference('split', [status(esa)], ['13'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (((r1_tarski @ sk_B @ sk_C_1)
% 0.43/0.62        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.43/0.62      inference('split', [status(esa)], ['16'])).
% 0.43/0.62  thf(t85_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X2 @ X3)
% 0.43/0.62          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.43/0.62         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.43/0.62         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.43/0.62      inference('split', [status(esa)], ['13'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.43/0.62         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.43/0.62       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['19', '22'])).
% 0.43/0.62  thf('24', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['15', '23'])).
% 0.43/0.62  thf('25', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['14', '24'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62          (k4_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('clc', [status(thm)], ['12', '25'])).
% 0.43/0.62  thf('27', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_k3_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]:
% 0.43/0.62         ((m1_subset_1 @ (k3_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.43/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf(d2_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X13 @ X14)
% 0.43/0.62          | (r2_hidden @ X13 @ X14)
% 0.43/0.62          | (v1_xboole_0 @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.62        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf(fc1_subset_1, axiom,
% 0.43/0.62    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.62  thf('32', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf(d1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ X10)
% 0.43/0.62          | (r1_tarski @ X11 @ X9)
% 0.43/0.62          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X9 : $i, X11 : $i]:
% 0.43/0.62         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.43/0.62  thf('36', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.43/0.62      inference('sup-', [status(thm)], ['33', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('38', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_A)),
% 0.43/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.43/0.62      inference('split', [status(esa)], ['16'])).
% 0.43/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.43/0.62       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.43/0.62      inference('split', [status(esa)], ['16'])).
% 0.43/0.62  thf('45', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['15', '23', '44'])).
% 0.43/0.62  thf('46', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 0.43/0.62  thf(t86_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.43/0.62       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X5 @ X6)
% 0.43/0.62          | ~ (r1_xboole_0 @ X5 @ X7)
% 0.43/0.62          | (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.62           (k4_xboole_0 @ X0 @ sk_B))
% 0.43/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['38', '48'])).
% 0.43/0.62  thf('50', plain, ($false), inference('demod', [status(thm)], ['26', '49'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
