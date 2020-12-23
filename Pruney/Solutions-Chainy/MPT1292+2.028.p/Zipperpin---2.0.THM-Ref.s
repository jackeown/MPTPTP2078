%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swt1JVZvxY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  203 ( 449 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ ( k3_tarski @ X31 ) )
      | ~ ( m1_setfam_1 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('5',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k3_tarski @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['3','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','18'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['21','24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swt1JVZvxY
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 18 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(t5_tops_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @
% 0.20/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.46                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @
% 0.20/0.46                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.46                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.20/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((m1_setfam_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d12_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X30 : $i, X31 : $i]:
% 0.20/0.46         ((r1_tarski @ X30 @ (k3_tarski @ X31)) | ~ (m1_setfam_1 @ X31 @ X30))),
% 0.20/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.20/0.46  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.46  thf('4', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.46  thf('5', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain, (((k3_tarski @ sk_B) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.46  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '7'])).
% 0.20/0.46  thf(t28_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.46  thf(t12_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X33 : $i, X34 : $i]:
% 0.20/0.46         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.20/0.46          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.46         = (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.46  thf(t2_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.46  thf('14', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_B) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X33 : $i, X34 : $i]:
% 0.20/0.46         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X2 : $i]: ((k1_setfam_1 @ (k2_tarski @ X2 @ sk_B)) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '18'])).
% 0.20/0.46  thf(fc2_struct_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X35 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 0.20/0.46          | ~ (l1_struct_0 @ X35)
% 0.20/0.46          | (v2_struct_0 @ X35))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.46  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('23', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('26', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['21', '24', '25'])).
% 0.20/0.46  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
