%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ACuhawrCxD

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  339 ( 639 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X7 @ X9 )
        = ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

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

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ( v1_tops_2 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ~ ( v1_tops_2 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['4','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ACuhawrCxD
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 116 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(t21_tops_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @
% 0.20/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @
% 0.20/0.54                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54               ( ( v1_tops_2 @ B @ A ) =>
% 0.20/0.54                 ( v1_tops_2 @
% 0.20/0.54                   ( k9_subset_1 @
% 0.20/0.54                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.20/0.54                   A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( l1_pre_topc @ A ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( m1_subset_1 @
% 0.20/0.54                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @
% 0.20/0.54                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54                  ( ( v1_tops_2 @ B @ A ) =>
% 0.20/0.54                    ( v1_tops_2 @
% 0.20/0.54                      ( k9_subset_1 @
% 0.20/0.54                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.20/0.54                      A ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (~ (v1_tops_2 @ 
% 0.20/0.54          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.20/0.54          sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.20/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('4', plain, (~ (v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.54  thf(t48_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.20/0.54           = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k7_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.54          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (m1_subset_1 @ 
% 0.20/0.54          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 0.20/0.54          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.54          | ((k7_subset_1 @ X8 @ X7 @ X9) = (k4_xboole_0 @ X7 @ X9)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.20/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.20/0.54          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.54  thf(t18_tops_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @
% 0.20/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @
% 0.20/0.54                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.54                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X13 @ 
% 0.20/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.20/0.54          | (v1_tops_2 @ X13 @ X14)
% 0.20/0.54          | ~ (r1_tarski @ X13 @ X15)
% 0.20/0.54          | ~ (v1_tops_2 @ X15 @ X14)
% 0.20/0.54          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.20/0.54          | ~ (l1_pre_topc @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.20/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.20/0.54          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.20/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.20/0.54          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.20/0.54          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('20', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]: (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.20/0.54      inference('sup+', [status(thm)], ['5', '21'])).
% 0.20/0.54  thf('23', plain, ($false), inference('demod', [status(thm)], ['4', '22'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
