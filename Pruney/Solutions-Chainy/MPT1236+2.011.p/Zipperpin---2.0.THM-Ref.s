%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ExrFKa1Vn

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 220 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( ( k1_struct_0 @ X5 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( ( k1_struct_0 @ X5 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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

thf('7',plain,(
    ( k1_tops_1 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( k1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_tops_1 @ sk_A @ k1_xboole_0 )
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k1_xboole_0
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ExrFKa1Vn
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:01:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 28 iterations in 0.018s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.46  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.46  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(d2_struct_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         (((k1_struct_0 @ X5) = (k1_xboole_0)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.46  thf(t4_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(t44_tops_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.46          | (r1_tarski @ (k1_tops_1 @ X8 @ X7) @ X7)
% 0.20/0.46          | ~ (l1_pre_topc @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X0)
% 0.20/0.46          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t3_xboole_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X0)
% 0.20/0.46          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         (((k1_struct_0 @ X5) = (k1_xboole_0)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.46  thf(t47_tops_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( l1_pre_topc @ A ) =>
% 0.20/0.46          ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t47_tops_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((k1_tops_1 @ sk_A @ (k1_struct_0 @ sk_A)) != (k1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))
% 0.20/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_l1_pre_topc, axiom,
% 0.20/0.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.46  thf('10', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.46  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '12'])).
% 0.20/0.46  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain, (((k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '15'])).
% 0.20/0.46  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
