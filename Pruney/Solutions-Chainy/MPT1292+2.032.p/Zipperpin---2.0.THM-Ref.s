%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PbYOceDD8j

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 414 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t5_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
              & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
                & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( m1_setfam_1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['3','7'])).

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
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['8','12'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( sk_B @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('17',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( sk_B @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('19',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( X1 = sk_B_1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['15','22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PbYOceDD8j
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:21:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 21 iterations in 0.013s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.46  thf(t5_tops_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @
% 0.19/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.46                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( m1_subset_1 @
% 0.19/0.46                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.46                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.19/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d12_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (m1_setfam_1 @ X4 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.19/0.46  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.46  thf('4', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.19/0.46  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.46  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '7'])).
% 0.19/0.46  thf(t3_xboole_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.46  thf('10', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (sk_B_1)) | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('13', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '12'])).
% 0.19/0.46  thf(fc2_struct_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X6 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.19/0.46          | ~ (l1_struct_0 @ X6)
% 0.19/0.46          | (v2_struct_0 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ sk_B_1)
% 0.19/0.46        | (v2_struct_0 @ sk_A)
% 0.19/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf(rc2_subset_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ?[B:$i]:
% 0.19/0.46       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.19/0.46  thf('16', plain, (![X2 : $i]: (v1_xboole_0 @ (sk_B @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.19/0.46  thf('17', plain, (![X2 : $i]: (v1_xboole_0 @ (sk_B @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.19/0.46  thf(t6_boole, axiom,
% 0.19/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t6_boole])).
% 0.19/0.46  thf('19', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('20', plain, (![X1 : $i]: (((X1) = (sk_B_1)) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain, (![X0 : $i]: ((sk_B @ X0) = (sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '20'])).
% 0.19/0.46  thf('22', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.19/0.46      inference('demod', [status(thm)], ['16', '21'])).
% 0.19/0.46  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('24', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '22', '23'])).
% 0.19/0.46  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
