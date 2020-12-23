%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ak93KDugXq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:20 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  314 ( 619 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t21_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X4 @ X2 @ X3 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ B )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ~ ( v1_tops_2 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['4','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ak93KDugXq
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:59:35 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 31 iterations in 0.020s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.18/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.18/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.18/0.45  thf(t21_tops_2, conjecture,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( l1_pre_topc @ A ) =>
% 0.18/0.45       ( ![B:$i]:
% 0.18/0.45         ( ( m1_subset_1 @
% 0.18/0.45             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45           ( ![C:$i]:
% 0.18/0.45             ( ( m1_subset_1 @
% 0.18/0.45                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45               ( ( v1_tops_2 @ B @ A ) =>
% 0.18/0.45                 ( v1_tops_2 @
% 0.18/0.45                   ( k9_subset_1 @
% 0.18/0.45                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.18/0.45                   A ) ) ) ) ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i]:
% 0.18/0.45        ( ( l1_pre_topc @ A ) =>
% 0.18/0.45          ( ![B:$i]:
% 0.18/0.45            ( ( m1_subset_1 @
% 0.18/0.45                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45              ( ![C:$i]:
% 0.18/0.45                ( ( m1_subset_1 @
% 0.18/0.45                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45                  ( ( v1_tops_2 @ B @ A ) =>
% 0.18/0.45                    ( v1_tops_2 @
% 0.18/0.45                      ( k9_subset_1 @
% 0.18/0.45                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.18/0.45                      A ) ) ) ) ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (~ (v1_tops_2 @ 
% 0.18/0.45          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.18/0.45          sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      ((m1_subset_1 @ sk_C @ 
% 0.18/0.45        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(redefinition_k9_subset_1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i]:
% 0.18/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.45       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.45         (((k9_subset_1 @ X4 @ X2 @ X3) = (k3_xboole_0 @ X2 @ X3))
% 0.18/0.45          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.18/0.45      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.18/0.45           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.18/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.45  thf('4', plain, (~ (v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.18/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      ((m1_subset_1 @ sk_B @ 
% 0.18/0.45        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t17_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.18/0.45  thf('6', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.18/0.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      ((m1_subset_1 @ sk_B @ 
% 0.18/0.45        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t3_tops_2, axiom,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( l1_struct_0 @ A ) =>
% 0.18/0.45       ( ![B:$i]:
% 0.18/0.45         ( ( m1_subset_1 @
% 0.18/0.45             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45           ( ![C:$i]:
% 0.18/0.45             ( ( r1_tarski @ C @ B ) =>
% 0.18/0.45               ( m1_subset_1 @
% 0.18/0.45                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.18/0.45         (~ (m1_subset_1 @ X9 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.18/0.45          | (m1_subset_1 @ X11 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.18/0.45          | ~ (r1_tarski @ X11 @ X9)
% 0.18/0.45          | ~ (l1_struct_0 @ X10))),
% 0.18/0.45      inference('cnf', [status(esa)], [t3_tops_2])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (l1_struct_0 @ sk_A)
% 0.18/0.45          | ~ (r1_tarski @ X0 @ sk_B)
% 0.18/0.45          | (m1_subset_1 @ X0 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.18/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.45  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(dt_l1_pre_topc, axiom,
% 0.18/0.45    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.18/0.45  thf('11', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.18/0.45      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.45  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.18/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.45  thf('13', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (r1_tarski @ X0 @ sk_B)
% 0.18/0.45          | (m1_subset_1 @ X0 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.18/0.45      inference('demod', [status(thm)], ['9', '12'])).
% 0.18/0.45  thf('14', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.18/0.45          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.45      inference('sup-', [status(thm)], ['6', '13'])).
% 0.18/0.45  thf(t18_tops_2, axiom,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( l1_pre_topc @ A ) =>
% 0.18/0.45       ( ![B:$i]:
% 0.18/0.45         ( ( m1_subset_1 @
% 0.18/0.45             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45           ( ![C:$i]:
% 0.18/0.45             ( ( m1_subset_1 @
% 0.18/0.45                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.45               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.18/0.45                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.18/0.45  thf('15', plain,
% 0.18/0.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.45         (~ (m1_subset_1 @ X6 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.18/0.45          | (v1_tops_2 @ X6 @ X7)
% 0.18/0.45          | ~ (r1_tarski @ X6 @ X8)
% 0.18/0.45          | ~ (v1_tops_2 @ X8 @ X7)
% 0.18/0.45          | ~ (m1_subset_1 @ X8 @ 
% 0.18/0.45               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.18/0.45          | ~ (l1_pre_topc @ X7))),
% 0.18/0.45      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.18/0.45  thf('16', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (~ (l1_pre_topc @ sk_A)
% 0.18/0.45          | ~ (m1_subset_1 @ X1 @ 
% 0.18/0.45               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.18/0.45          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.18/0.45          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 0.18/0.45          | (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.18/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.45  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('18', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (~ (m1_subset_1 @ X1 @ 
% 0.18/0.45             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.18/0.45          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.18/0.45          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 0.18/0.45          | (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['16', '17'])).
% 0.18/0.45  thf('19', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.18/0.45          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.18/0.45          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.18/0.45      inference('sup-', [status(thm)], ['5', '18'])).
% 0.18/0.45  thf('20', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.18/0.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.18/0.45  thf('21', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('22', plain,
% 0.18/0.45      (![X0 : $i]: (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.18/0.45      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.18/0.45  thf('23', plain, ($false), inference('demod', [status(thm)], ['4', '22'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
