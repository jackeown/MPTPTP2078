%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ax1H2qazm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 207 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  343 (1891 expanded)
%              Number of equality atoms :   38 ( 190 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( m1_setfam_1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( ( k3_tarski @ X18 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('7',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X18: $i] :
      ( ( ( k3_tarski @ X18 )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_tarski @ X8 @ X6 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
        = sk_B_1 )
      | ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = sk_B_1 )
      | ~ ( r1_tarski @ X4 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) )
      = sk_B_1 )
    | ( ( sk_B @ ( k1_zfmisc_1 @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X18: $i] :
      ( ( ( k3_tarski @ X18 )
        = k1_xboole_0 )
      | ( ( sk_B @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('18',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( ( k3_tarski @ X18 )
        = sk_B_1 )
      | ( ( sk_B @ X18 )
       != sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['16','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B_1 @ X3 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X10 ) @ ( k3_tarski @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_B_1 ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ sk_B_1 ) )
      | ( ( k3_tarski @ X0 )
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_B_1 ) )
    | ( ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) )
      = ( k3_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B_1 @ X3 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('31',plain,
    ( ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['16','20'])).

thf('32',plain,
    ( sk_B_1
    = ( k3_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B_1 @ X3 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('34',plain,
    ( sk_B_1
    = ( k3_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('35',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','32','33','34'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ax1H2qazm
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 56 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.20/0.47  thf(t5_tops_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @
% 0.20/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.47                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @
% 0.20/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.47                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d12_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (m1_setfam_1 @ X13 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.20/0.47  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((~ (r1_tarski @ (k3_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ((k3_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(t91_orders_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47            ( ![B:$i]:
% 0.20/0.47              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.20/0.47       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.47            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         (((k3_tarski @ X18) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.20/0.47  thf('7', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         (((k3_tarski @ X18) = (sk_B_1)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(d1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X8 @ X7)
% 0.20/0.47          | (r1_tarski @ X8 @ X6)
% 0.20/0.47          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i]:
% 0.20/0.47         ((r1_tarski @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k3_tarski @ (k1_zfmisc_1 @ X0)) = (sk_B_1))
% 0.20/0.47          | (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.47  thf(t3_xboole_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.47  thf('13', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X4 : $i]: (((X4) = (sk_B_1)) | ~ (r1_tarski @ X4 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((((k3_tarski @ (k1_zfmisc_1 @ sk_B_1)) = (sk_B_1))
% 0.20/0.47        | ((sk_B @ (k1_zfmisc_1 @ sk_B_1)) = (sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         (((k3_tarski @ X18) = (k1_xboole_0)) | ((sk_B @ X18) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.20/0.47  thf('18', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         (((k3_tarski @ X18) = (sk_B_1)) | ((sk_B @ X18) != (sk_B_1)))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.47  thf('21', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_B_1)) = (sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['16', '20'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('22', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('23', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, (![X3 : $i]: (r1_tarski @ sk_B_1 @ X3)),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf(t95_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         ((r1_tarski @ (k3_tarski @ X10) @ (k3_tarski @ X11))
% 0.20/0.47          | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]: (r1_tarski @ (k3_tarski @ sk_B_1) @ (k3_tarski @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ sk_B_1))
% 0.20/0.47          | ((k3_tarski @ X0) = (k3_tarski @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_B_1 @ (k3_tarski @ sk_B_1))
% 0.20/0.47        | ((k3_tarski @ (k1_zfmisc_1 @ sk_B_1)) = (k3_tarski @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '28'])).
% 0.20/0.47  thf('30', plain, (![X3 : $i]: (r1_tarski @ sk_B_1 @ X3)),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('31', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_B_1)) = (sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['16', '20'])).
% 0.20/0.47  thf('32', plain, (((sk_B_1) = (k3_tarski @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.47  thf('33', plain, (![X3 : $i]: (r1_tarski @ sk_B_1 @ X3)),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('34', plain, (((sk_B_1) = (k3_tarski @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.47  thf('35', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '32', '33', '34'])).
% 0.20/0.47  thf(fc2_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X15 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.20/0.47          | ~ (l1_struct_0 @ X15)
% 0.20/0.47          | (v2_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.47  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.47  thf('39', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.20/0.47  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
