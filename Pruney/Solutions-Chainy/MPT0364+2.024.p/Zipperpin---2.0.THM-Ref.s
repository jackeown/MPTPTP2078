%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.haDkeKfkaG

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 114 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  335 (1176 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X6 @ ( k3_subset_1 @ X5 @ X4 ) )
      | ( r1_xboole_0 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','18','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_xboole_0 @ X6 @ X4 )
      | ( r1_tarski @ X6 @ ( k3_subset_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['20','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.haDkeKfkaG
% 0.17/0.37  % Computer   : n021.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 20:24:35 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 36 iterations in 0.016s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.47  thf(t44_subset_1, conjecture,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47       ( ![C:$i]:
% 0.23/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.23/0.47             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.47    (~( ![A:$i,B:$i]:
% 0.23/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47          ( ![C:$i]:
% 0.23/0.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.23/0.47                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.23/0.47  thf('0', plain,
% 0.23/0.47      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.23/0.47        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('1', plain,
% 0.23/0.47      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.47      inference('split', [status(esa)], ['0'])).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.23/0.47       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('split', [status(esa)], ['0'])).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      (((r1_tarski @ sk_B @ sk_C)
% 0.23/0.47        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('4', plain,
% 0.23/0.47      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('6', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(dt_k3_subset_1, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.47  thf('7', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i]:
% 0.23/0.47         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.23/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.47  thf('8', plain,
% 0.23/0.47      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.47  thf(t43_subset_1, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47       ( ![C:$i]:
% 0.23/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.23/0.47             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.23/0.47          | ~ (r1_tarski @ X6 @ (k3_subset_1 @ X5 @ X4))
% 0.23/0.47          | (r1_xboole_0 @ X6 @ X4)
% 0.23/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.47      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.23/0.47  thf('10', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.47          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.23/0.47          | ~ (r1_tarski @ X0 @ 
% 0.23/0.47               (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.47  thf('11', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(involutiveness_k3_subset_1, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.47       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.23/0.47  thf('12', plain,
% 0.23/0.47      (![X2 : $i, X3 : $i]:
% 0.23/0.47         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.23/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.23/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.47  thf('13', plain,
% 0.23/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.23/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.47  thf('14', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.47          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.23/0.47          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.23/0.47      inference('demod', [status(thm)], ['10', '13'])).
% 0.23/0.47  thf('15', plain,
% 0.23/0.47      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.23/0.47        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['5', '14'])).
% 0.23/0.47  thf('16', plain,
% 0.23/0.47      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['4', '15'])).
% 0.23/0.47  thf('17', plain,
% 0.23/0.47      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('split', [status(esa)], ['0'])).
% 0.23/0.47  thf('18', plain,
% 0.23/0.47      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.23/0.47       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.47  thf('19', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.47      inference('sat_resolution*', [status(thm)], ['2', '18'])).
% 0.23/0.47  thf('20', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.23/0.47      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.23/0.47  thf('21', plain,
% 0.23/0.47      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.47         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('22', plain,
% 0.23/0.47      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.23/0.47       ((r1_tarski @ sk_B @ sk_C))),
% 0.23/0.47      inference('split', [status(esa)], ['3'])).
% 0.23/0.47  thf('23', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('sat_resolution*', [status(thm)], ['2', '18', '22'])).
% 0.23/0.47  thf('24', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.47      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.23/0.47  thf('25', plain,
% 0.23/0.47      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.47  thf('26', plain,
% 0.23/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.23/0.47          | ~ (r1_xboole_0 @ X6 @ X4)
% 0.23/0.47          | (r1_tarski @ X6 @ (k3_subset_1 @ X5 @ X4))
% 0.23/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.47      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.23/0.47  thf('27', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.47          | (r1_tarski @ X0 @ 
% 0.23/0.47             (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.23/0.47          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.47  thf('28', plain,
% 0.23/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.23/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.47  thf('29', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.47          | (r1_tarski @ X0 @ sk_C)
% 0.23/0.47          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.47  thf('30', plain,
% 0.23/0.47      (((r1_tarski @ sk_B @ sk_C)
% 0.23/0.47        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['24', '29'])).
% 0.23/0.47  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('32', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.23/0.47      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.47  thf('33', plain, ($false), inference('demod', [status(thm)], ['20', '32'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
