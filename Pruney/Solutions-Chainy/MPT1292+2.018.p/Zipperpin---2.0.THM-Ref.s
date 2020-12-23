%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xEhmcdyx7b

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:03 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  195 ( 380 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_setfam_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_setfam_1 @ o_0_0_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( m1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('7',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( k3_tarski @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','11'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( u1_struct_0 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['12','16'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( ( k1_struct_0 @ X4 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( ( k1_struct_0 @ X4 )
        = o_0_0_xboole_0 )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_struct_0 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['19','28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xEhmcdyx7b
% 0.10/0.30  % Computer   : n005.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 09:39:03 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.30  % Python version: Python 3.6.8
% 0.10/0.30  % Running in FO mode
% 0.15/0.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.15/0.42  % Solved by: fo/fo7.sh
% 0.15/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.15/0.42  % done 20 iterations in 0.012s
% 0.15/0.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.15/0.42  % SZS output start Refutation
% 0.15/0.42  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.15/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.15/0.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.15/0.42  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.15/0.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.15/0.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.15/0.42  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.15/0.42  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.15/0.42  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.15/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.15/0.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.15/0.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.15/0.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.15/0.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.15/0.42  thf(t5_tops_2, conjecture,
% 0.15/0.42    (![A:$i]:
% 0.15/0.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.15/0.42       ( ![B:$i]:
% 0.15/0.42         ( ( m1_subset_1 @
% 0.15/0.42             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.15/0.42           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.15/0.42                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.15/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.15/0.42    (~( ![A:$i]:
% 0.15/0.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.15/0.42          ( ![B:$i]:
% 0.15/0.42            ( ( m1_subset_1 @
% 0.15/0.42                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.15/0.42              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.15/0.42                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.15/0.42    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.15/0.42  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf('1', plain, ((m1_setfam_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.15/0.42  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf('4', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('sup+', [status(thm)], ['2', '3'])).
% 0.15/0.42  thf('5', plain, ((m1_setfam_1 @ o_0_0_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.15/0.42      inference('demod', [status(thm)], ['1', '4'])).
% 0.15/0.42  thf(d12_setfam_1, axiom,
% 0.15/0.42    (![A:$i,B:$i]:
% 0.15/0.42     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.15/0.42  thf('6', plain,
% 0.15/0.42      (![X1 : $i, X2 : $i]:
% 0.15/0.42         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (m1_setfam_1 @ X2 @ X1))),
% 0.15/0.42      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.15/0.42  thf('7', plain,
% 0.15/0.42      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ o_0_0_xboole_0))),
% 0.15/0.42      inference('sup-', [status(thm)], ['5', '6'])).
% 0.15/0.42  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.15/0.42  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.15/0.42  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('11', plain, (((k3_tarski @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.15/0.42  thf('12', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ o_0_0_xboole_0)),
% 0.15/0.42      inference('demod', [status(thm)], ['7', '11'])).
% 0.15/0.42  thf(t3_xboole_1, axiom,
% 0.15/0.42    (![A:$i]:
% 0.15/0.42     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.15/0.42  thf('13', plain,
% 0.15/0.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.15/0.42  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('16', plain,
% 0.15/0.42      (![X0 : $i]:
% 0.15/0.42         (((X0) = (o_0_0_xboole_0)) | ~ (r1_tarski @ X0 @ o_0_0_xboole_0))),
% 0.15/0.42      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.15/0.42  thf('17', plain, (((u1_struct_0 @ sk_A) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('sup-', [status(thm)], ['12', '16'])).
% 0.15/0.42  thf(fc2_struct_0, axiom,
% 0.15/0.42    (![A:$i]:
% 0.15/0.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.15/0.42       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.15/0.42  thf('18', plain,
% 0.15/0.42      (![X5 : $i]:
% 0.15/0.42         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.15/0.42          | ~ (l1_struct_0 @ X5)
% 0.15/0.42          | (v2_struct_0 @ X5))),
% 0.15/0.42      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.15/0.42  thf('19', plain,
% 0.15/0.42      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.15/0.42        | (v2_struct_0 @ sk_A)
% 0.15/0.42        | ~ (l1_struct_0 @ sk_A))),
% 0.15/0.42      inference('sup-', [status(thm)], ['17', '18'])).
% 0.15/0.42  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf(d2_struct_0, axiom,
% 0.15/0.42    (![A:$i]:
% 0.15/0.42     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.15/0.42  thf('21', plain,
% 0.15/0.42      (![X4 : $i]:
% 0.15/0.42         (((k1_struct_0 @ X4) = (k1_xboole_0)) | ~ (l1_struct_0 @ X4))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.15/0.42  thf('22', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.15/0.42  thf('23', plain,
% 0.15/0.42      (![X4 : $i]:
% 0.15/0.42         (((k1_struct_0 @ X4) = (o_0_0_xboole_0)) | ~ (l1_struct_0 @ X4))),
% 0.15/0.42      inference('demod', [status(thm)], ['21', '22'])).
% 0.15/0.42  thf('24', plain, (((k1_struct_0 @ sk_A) = (o_0_0_xboole_0))),
% 0.15/0.42      inference('sup-', [status(thm)], ['20', '23'])).
% 0.15/0.42  thf(fc3_struct_0, axiom,
% 0.15/0.42    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.15/0.42  thf('25', plain,
% 0.15/0.42      (![X6 : $i]: ((v1_xboole_0 @ (k1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.15/0.42      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.15/0.42  thf('26', plain, (((v1_xboole_0 @ o_0_0_xboole_0) | ~ (l1_struct_0 @ sk_A))),
% 0.15/0.42      inference('sup+', [status(thm)], ['24', '25'])).
% 0.15/0.42  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf('28', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.15/0.42      inference('demod', [status(thm)], ['26', '27'])).
% 0.15/0.42  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.15/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.42  thf('30', plain, ((v2_struct_0 @ sk_A)),
% 0.15/0.42      inference('demod', [status(thm)], ['19', '28', '29'])).
% 0.15/0.42  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.15/0.42  
% 0.15/0.42  % SZS output end Refutation
% 0.15/0.42  
% 0.15/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
