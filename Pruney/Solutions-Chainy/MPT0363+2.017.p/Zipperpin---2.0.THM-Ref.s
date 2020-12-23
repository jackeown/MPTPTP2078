%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSRTEwMO69

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 107 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  343 ( 928 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['14'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('23',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['14'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['20','29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['19','31'])).

thf('33',plain,
    ( $false
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['20','29'])).

thf('35',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSRTEwMO69
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:24:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 43 iterations in 0.021s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(t43_subset_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.19/0.47             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47          ( ![C:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.19/0.47                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.19/0.47        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.19/0.47         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d5_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X16 : $i, X17 : $i]:
% 0.19/0.47         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.19/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d2_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X13 @ X14)
% 0.19/0.47          | (r2_hidden @ X13 @ X14)
% 0.19/0.47          | (v1_xboole_0 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.47        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf(fc1_subset_1, axiom,
% 0.19/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.47  thf('8', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.47  thf('9', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf(l49_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]:
% 0.19/0.47         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.47  thf('11', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf(t99_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.47  thf('12', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.47  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.19/0.47        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['14'])).
% 0.19/0.47  thf(t86_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.19/0.47       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (r1_tarski @ X7 @ X8)
% 0.19/0.47          | ~ (r1_xboole_0 @ X7 @ X9)
% 0.19/0.47          | (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      ((![X0 : $i]:
% 0.19/0.47          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.19/0.47           | ~ (r1_tarski @ sk_B @ X0)))
% 0.19/0.47         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.19/0.47         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.19/0.47         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['4', '18'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.19/0.47       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf(t79_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.19/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.47  thf('23', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_C)),
% 0.19/0.47      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.19/0.47         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['14'])).
% 0.19/0.47  thf(t63_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.47       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         (~ (r1_tarski @ X2 @ X3)
% 0.19/0.47          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.19/0.47          | (r1_xboole_0 @ X2 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      ((![X0 : $i]:
% 0.19/0.47          ((r1_xboole_0 @ sk_B @ X0)
% 0.19/0.47           | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0)))
% 0.19/0.47         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.19/0.47         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.19/0.47       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_B @ sk_C)) | 
% 0.19/0.47       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['14'])).
% 0.19/0.47  thf('31', plain, (((r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['20', '29', '30'])).
% 0.19/0.47  thf('32', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['19', '31'])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (($false) <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.19/0.47      inference('demod', [status(thm)], ['1', '32'])).
% 0.19/0.47  thf('34', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['20', '29'])).
% 0.19/0.47  thf('35', plain, ($false),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['33', '34'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
