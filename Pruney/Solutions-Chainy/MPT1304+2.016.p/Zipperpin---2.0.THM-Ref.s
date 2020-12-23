%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LzwKkyFkx0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:23 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  307 ( 569 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t22_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k7_subset_1 @ X6 @ X5 @ X7 )
        = ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v1_tops_2 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( v1_tops_2 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['4','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LzwKkyFkx0
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:49:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.18/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.50  % Solved by: fo/fo7.sh
% 0.18/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.50  % done 99 iterations in 0.065s
% 0.18/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.50  % SZS output start Refutation
% 0.18/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.18/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.50  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.18/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.50  thf(t22_tops_2, conjecture,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( l1_pre_topc @ A ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_subset_1 @
% 0.18/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50           ( ![C:$i]:
% 0.18/0.50             ( ( m1_subset_1 @
% 0.18/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50               ( ( v1_tops_2 @ B @ A ) =>
% 0.18/0.50                 ( v1_tops_2 @
% 0.18/0.50                   ( k7_subset_1 @
% 0.18/0.50                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.18/0.50                   A ) ) ) ) ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i]:
% 0.18/0.50        ( ( l1_pre_topc @ A ) =>
% 0.18/0.50          ( ![B:$i]:
% 0.18/0.50            ( ( m1_subset_1 @
% 0.18/0.50                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50              ( ![C:$i]:
% 0.18/0.50                ( ( m1_subset_1 @
% 0.18/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50                  ( ( v1_tops_2 @ B @ A ) =>
% 0.18/0.50                    ( v1_tops_2 @
% 0.18/0.50                      ( k7_subset_1 @
% 0.18/0.50                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.18/0.50                      A ) ) ) ) ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 0.18/0.50  thf('0', plain,
% 0.18/0.50      (~ (v1_tops_2 @ 
% 0.18/0.50          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.18/0.50          sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('1', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_B @ 
% 0.18/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.18/0.50  thf('2', plain,
% 0.18/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.18/0.50          | ((k7_subset_1 @ X6 @ X5 @ X7) = (k4_xboole_0 @ X5 @ X7)))),
% 0.18/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.18/0.50  thf('3', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.18/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.50  thf('4', plain, (~ (v1_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.18/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.50  thf('5', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_B @ 
% 0.18/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('6', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B @ 
% 0.18/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(t3_subset, axiom,
% 0.18/0.51    (![A:$i,B:$i]:
% 0.18/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.51  thf('7', plain,
% 0.18/0.51      (![X8 : $i, X9 : $i]:
% 0.18/0.51         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.18/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.51  thf('8', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.51  thf(t36_xboole_1, axiom,
% 0.18/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.18/0.51  thf('9', plain,
% 0.18/0.51      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.18/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.18/0.51  thf(t1_xboole_1, axiom,
% 0.18/0.51    (![A:$i,B:$i,C:$i]:
% 0.18/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.18/0.51       ( r1_tarski @ A @ C ) ))).
% 0.18/0.51  thf('10', plain,
% 0.18/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.18/0.51          | ~ (r1_tarski @ X1 @ X2)
% 0.18/0.51          | (r1_tarski @ X0 @ X2))),
% 0.18/0.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.18/0.51  thf('11', plain,
% 0.18/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.51         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.51  thf('12', plain,
% 0.18/0.51      (![X0 : $i]:
% 0.18/0.51         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.18/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.18/0.51  thf('13', plain,
% 0.18/0.51      (![X8 : $i, X10 : $i]:
% 0.18/0.51         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.18/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.51  thf('14', plain,
% 0.18/0.51      (![X0 : $i]:
% 0.18/0.51         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.18/0.51          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.51  thf(t18_tops_2, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( l1_pre_topc @ A ) =>
% 0.18/0.51       ( ![B:$i]:
% 0.18/0.51         ( ( m1_subset_1 @
% 0.18/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.51           ( ![C:$i]:
% 0.18/0.51             ( ( m1_subset_1 @
% 0.18/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.51               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.18/0.51                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.18/0.51  thf('15', plain,
% 0.18/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X11 @ 
% 0.18/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.18/0.51          | (v1_tops_2 @ X11 @ X12)
% 0.18/0.51          | ~ (r1_tarski @ X11 @ X13)
% 0.18/0.51          | ~ (v1_tops_2 @ X13 @ X12)
% 0.18/0.51          | ~ (m1_subset_1 @ X13 @ 
% 0.18/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.18/0.51          | ~ (l1_pre_topc @ X12))),
% 0.18/0.51      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.18/0.51  thf('16', plain,
% 0.18/0.51      (![X0 : $i, X1 : $i]:
% 0.18/0.51         (~ (l1_pre_topc @ sk_A)
% 0.18/0.51          | ~ (m1_subset_1 @ X1 @ 
% 0.18/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.18/0.51          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.18/0.51          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.18/0.51          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.51  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('18', plain,
% 0.18/0.51      (![X0 : $i, X1 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.18/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.18/0.51          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.18/0.51          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.18/0.51          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.18/0.51  thf('19', plain,
% 0.18/0.51      (![X0 : $i]:
% 0.18/0.51         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.18/0.51          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.18/0.51          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['5', '18'])).
% 0.18/0.51  thf('20', plain,
% 0.18/0.51      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.18/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.18/0.51  thf('21', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('22', plain,
% 0.18/0.51      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.18/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.18/0.51  thf('23', plain, ($false), inference('demod', [status(thm)], ['4', '22'])).
% 0.18/0.51  
% 0.18/0.51  % SZS output end Refutation
% 0.18/0.51  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
