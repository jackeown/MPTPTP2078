%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5QBvhPSOJ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  350 ( 943 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['6','16'])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['5','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['6','16','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['18','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5QBvhPSOJ
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 64 iterations in 0.042s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(t43_subset_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.52             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52          ( ![C:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.52                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.21/0.52        | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.21/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d5_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.21/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.21/0.52       ~ ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf(t79_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X4)),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.21/0.52        | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.21/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('split', [status(esa)], ['9'])).
% 0.21/0.52  thf(t63_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.52       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.21/0.52          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((r1_xboole_0 @ sk_B @ X0)
% 0.21/0.52           | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)))
% 0.21/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 0.21/0.52           | (r1_xboole_0 @ sk_B @ X0)))
% 0.21/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_B @ sk_C_1))
% 0.21/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ sk_B @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_B @ sk_C_1)) | 
% 0.21/0.52       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['6', '16'])).
% 0.21/0.52  thf('18', plain, (~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['5', '17'])).
% 0.21/0.52  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d2_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X13 @ X14)
% 0.21/0.52          | (r2_hidden @ X13 @ X14)
% 0.21/0.52          | (v1_xboole_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.52        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf(fc1_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.52  thf('22', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.52  thf('23', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf(d1_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.52          | (r1_tarski @ X11 @ X9)
% 0.21/0.52          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X9 : $i, X11 : $i]:
% 0.21/0.52         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.52  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_B @ sk_C_1)) <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['9'])).
% 0.21/0.52  thf(t86_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.52       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.52          | ~ (r1_xboole_0 @ X5 @ X7)
% 0.21/0.52          | (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.21/0.52           | ~ (r1_tarski @ sk_B @ X0)))
% 0.21/0.52         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_B @ sk_C_1)) | 
% 0.21/0.52       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['9'])).
% 0.21/0.52  thf('31', plain, (((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['6', '16', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.21/0.52          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.21/0.52  thf('33', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.52  thf('34', plain, ($false), inference('demod', [status(thm)], ['18', '33'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
