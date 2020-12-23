%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qq7LqUjVKJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 ( 380 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t41_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( B
               != ( k1_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8
        = ( k1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t41_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

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

thf('15',plain,(
    ( k1_tops_1 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( k1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k1_tops_1 @ sk_A @ k1_xboole_0 )
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    k1_xboole_0
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qq7LqUjVKJ
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:18:21 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 18 iterations in 0.012s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.49  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.49  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.49  thf(t4_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf(t41_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ~( ( ( B ) != ( k1_struct_0 @ A ) ) & 
% 0.22/0.49                ( ![C:$i]:
% 0.22/0.49                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49                    ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | ((X8) = (k1_struct_0 @ X9))
% 0.22/0.49          | (r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 0.22/0.49          | ~ (l1_pre_topc @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t41_pre_topc])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.49          | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf(t5_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X5 @ X6)
% 0.22/0.49          | ~ (v1_xboole_0 @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k1_xboole_0) = (k1_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf(t44_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.49          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.22/0.49          | ~ (l1_pre_topc @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf(t3_xboole_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.49  thf(t47_tops_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t47_tops_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (((k1_tops_1 @ sk_A @ (k1_struct_0 @ sk_A)) != (k1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((((k1_xboole_0) != (k1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '18'])).
% 0.22/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain, (((k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '21'])).
% 0.22/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
