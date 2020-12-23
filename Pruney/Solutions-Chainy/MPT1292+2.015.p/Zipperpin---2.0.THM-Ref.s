%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UaZNT62hCE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 ( 606 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_setfam_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_setfam_1 @ X16 @ X15 )
      | ( ( k5_setfam_1 @ X15 @ X16 )
        = X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ X0 @ sk_B )
        = X0 )
      | ~ ( m1_setfam_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k5_setfam_1 @ X8 @ X7 )
        = ( k3_tarski @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B )
      = ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = X0 )
      | ~ ( m1_setfam_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k3_tarski @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k3_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_setfam_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B )
      = ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B @ X3 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_tarski @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['23','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['16','29','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UaZNT62hCE
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 43 iterations in 0.019s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.45  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(t5_tops_2, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @
% 0.21/0.45             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.45           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.45                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.45          ( ![B:$i]:
% 0.21/0.45            ( ( m1_subset_1 @
% 0.21/0.45                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.45              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.45                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.45  thf('0', plain, ((m1_setfam_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t4_subset_1, axiom,
% 0.21/0.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.45  thf('2', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('3', plain, (![X4 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X4))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(t60_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.45       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X15 : $i, X16 : $i]:
% 0.21/0.45         (~ (m1_setfam_1 @ X16 @ X15)
% 0.21/0.45          | ((k5_setfam_1 @ X15 @ X16) = (X15))
% 0.21/0.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.21/0.45      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k5_setfam_1 @ X0 @ sk_B) = (X0)) | ~ (m1_setfam_1 @ sk_B @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('6', plain, (![X4 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X4))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(redefinition_k5_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.45       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i]:
% 0.21/0.45         (((k5_setfam_1 @ X8 @ X7) = (k3_tarski @ X7))
% 0.21/0.45          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B) = (k3_tarski @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i]: (((k3_tarski @ sk_B) = (X0)) | ~ (m1_setfam_1 @ sk_B @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.45  thf('10', plain, (((k3_tarski @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.45  thf(fc2_struct_0, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.45       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X17 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.45          | ~ (l1_struct_0 @ X17)
% 0.21/0.45          | (v2_struct_0 @ X17))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      ((~ (v1_xboole_0 @ (k3_tarski @ sk_B))
% 0.21/0.45        | (v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.45  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      ((~ (v1_xboole_0 @ (k3_tarski @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.45  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('16', plain, (~ (v1_xboole_0 @ (k3_tarski @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain, (![X4 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X4))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(dt_k5_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.45       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i]:
% 0.21/0.45         ((m1_subset_1 @ (k5_setfam_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 0.21/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k5_setfam_1 @ X0 @ sk_B) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B) = (k3_tarski @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X0 : $i]: (m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (![X9 : $i, X10 : $i]:
% 0.21/0.45         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('23', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ sk_B) @ X0)),
% 0.21/0.45      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.45  thf('24', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.45  thf('25', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('26', plain, (![X3 : $i]: (r1_tarski @ sk_B @ X3)),
% 0.21/0.45      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.45  thf(d10_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('27', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('28', plain, (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.45  thf('29', plain, (((k3_tarski @ sk_B) = (sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.45  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.45  thf('31', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('32', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.45      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.45  thf('33', plain, ($false),
% 0.21/0.45      inference('demod', [status(thm)], ['16', '29', '32'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
