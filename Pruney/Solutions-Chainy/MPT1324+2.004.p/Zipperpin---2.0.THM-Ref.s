%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4GUs5BJNxT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  349 ( 598 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t45_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( k1_tops_2 @ A @ B @ C ) ) )
               => ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( k1_tops_2 @ A @ B @ C ) ) )
                 => ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_tops_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( k1_tops_2 @ A @ B @ C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X12 @ X11 ) ) @ ( k1_tops_2 @ X12 @ X11 @ X13 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X12 ) @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) )
    = ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4GUs5BJNxT
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:39:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 63 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(t45_tops_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @
% 0.22/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50               ( ( r1_tarski @
% 0.22/0.50                   B @ 
% 0.22/0.50                   ( k5_setfam_1 @
% 0.22/0.50                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.50                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.22/0.50                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_pre_topc @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( m1_subset_1 @
% 0.22/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50                  ( ( r1_tarski @
% 0.22/0.50                      B @ 
% 0.22/0.50                      ( k5_setfam_1 @
% 0.22/0.50                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.50                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.22/0.50                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t44_tops_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @
% 0.22/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50               ( r1_tarski @
% 0.22/0.50                 ( k5_setfam_1 @
% 0.22/0.50                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.50                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.22/0.50                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | (r1_tarski @ 
% 0.22/0.50             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X12 @ X11)) @ 
% 0.22/0.50              (k1_tops_2 @ X12 @ X11 @ X13)) @ 
% 0.22/0.50             (k5_setfam_1 @ (u1_struct_0 @ X12) @ X13))
% 0.22/0.50          | ~ (m1_subset_1 @ X13 @ 
% 0.22/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.22/0.50          | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | (r1_tarski @ 
% 0.22/0.50             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.22/0.50              (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.22/0.50             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ 
% 0.22/0.50           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.22/0.50            (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.22/0.50           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((r1_tarski @ 
% 0.22/0.50        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.50        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf(t8_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.22/0.50       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.50          | ~ (r1_tarski @ X10 @ X9)
% 0.22/0.50          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((r1_tarski @ 
% 0.22/0.50        (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.22/0.50         (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50          (k1_tops_2 @ sk_A @ sk_B @ sk_C))) @ 
% 0.22/0.50        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '11'])).
% 0.22/0.50  thf(t7_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.22/0.50          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.22/0.50         (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50          (k1_tops_2 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.50         = (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((r1_tarski @ sk_B @ 
% 0.22/0.50        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50         (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t10_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (r1_tarski @ sk_B @ 
% 0.22/0.50          (k2_xboole_0 @ X0 @ 
% 0.22/0.50           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50            (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['16', '19'])).
% 0.22/0.50  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
