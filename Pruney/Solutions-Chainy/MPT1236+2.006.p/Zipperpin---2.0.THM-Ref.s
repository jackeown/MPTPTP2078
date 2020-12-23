%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z1lzKfDszw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 ( 273 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( ( k1_struct_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( ( ( k1_struct_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf(dt_k1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k1_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_struct_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X5 @ X4 ) @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( ( k1_struct_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf(t47_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) )
        = ( k1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) )
          = ( k1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_tops_1])).

thf('12',plain,(
    ( k1_tops_1 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( k1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k1_tops_1 @ sk_A @ k1_xboole_0 )
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k1_xboole_0
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    k1_xboole_0
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z1lzKfDszw
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:35:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 19 iterations in 0.015s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(d2_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         (((k1_struct_0 @ X1) = (k1_xboole_0)) | ~ (l1_struct_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         (((k1_struct_0 @ X1) = (k1_xboole_0)) | ~ (l1_struct_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.19/0.47  thf(dt_k1_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_struct_0 @ A ) =>
% 0.19/0.47       ( m1_subset_1 @
% 0.19/0.47         ( k1_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (k1_struct_0 @ X2) @ 
% 0.19/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.19/0.47          | ~ (l1_struct_0 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k1_struct_0])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.47          | ~ (l1_struct_0 @ X0)
% 0.19/0.47          | ~ (l1_struct_0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (l1_struct_0 @ X0)
% 0.19/0.47          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf(t44_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.47          | (r1_tarski @ (k1_tops_1 @ X5 @ X4) @ X4)
% 0.19/0.47          | ~ (l1_pre_topc @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (l1_struct_0 @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(dt_l1_pre_topc, axiom,
% 0.19/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.47  thf('7', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(t3_xboole_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X0)
% 0.19/0.47          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         (((k1_struct_0 @ X1) = (k1_xboole_0)) | ~ (l1_struct_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.19/0.47  thf(t47_tops_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( l1_pre_topc @ A ) =>
% 0.19/0.47          ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t47_tops_1])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (((k1_tops_1 @ sk_A @ (k1_struct_0 @ sk_A)) != (k1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('15', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.47  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '17'])).
% 0.19/0.47  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain, (((k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '20'])).
% 0.19/0.47  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
