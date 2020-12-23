%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXJ8ksU8j6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:26 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  315 ( 572 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t24_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t19_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v2_tops_2 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ~ ( v2_tops_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['4','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXJ8ksU8j6
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 361 iterations in 0.322s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.59/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(t24_tops_2, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( l1_pre_topc @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( m1_subset_1 @
% 0.59/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( m1_subset_1 @
% 0.59/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77               ( ( v2_tops_2 @ B @ A ) =>
% 0.59/0.77                 ( v2_tops_2 @
% 0.59/0.77                   ( k9_subset_1 @
% 0.59/0.77                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.59/0.77                   A ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( l1_pre_topc @ A ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( m1_subset_1 @
% 0.59/0.77                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77              ( ![C:$i]:
% 0.59/0.77                ( ( m1_subset_1 @
% 0.59/0.77                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77                  ( ( v2_tops_2 @ B @ A ) =>
% 0.59/0.77                    ( v2_tops_2 @
% 0.59/0.77                      ( k9_subset_1 @
% 0.59/0.77                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.59/0.77                      A ) ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (~ (v2_tops_2 @ 
% 0.59/0.77          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.59/0.77          sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.77         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.59/0.77          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.59/0.77           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf('4', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '3'])).
% 0.59/0.77  thf(t48_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.59/0.77           = (k3_xboole_0 @ X5 @ X6))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t3_subset, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.77  thf('9', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.77  thf(t109_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.59/0.77          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X12 : $i, X14 : $i]:
% 0.59/0.77         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.59/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf(t19_tops_2, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( l1_pre_topc @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( m1_subset_1 @
% 0.59/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( m1_subset_1 @
% 0.59/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.77               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.59/0.77                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X15 @ 
% 0.59/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.59/0.77          | (v2_tops_2 @ X15 @ X16)
% 0.59/0.77          | ~ (r1_tarski @ X15 @ X17)
% 0.59/0.77          | ~ (v2_tops_2 @ X17 @ X16)
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ 
% 0.59/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.59/0.77          | ~ (l1_pre_topc @ X16))),
% 0.59/0.77      inference('cnf', [status(esa)], [t19_tops_2])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (l1_pre_topc @ sk_A)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ 
% 0.59/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.77          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.59/0.77          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.59/0.77          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.77  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ 
% 0.59/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.77          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.59/0.77          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.59/0.77          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.59/0.77          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.59/0.77          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['6', '17'])).
% 0.59/0.77  thf(t36_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('20', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X0 : $i]: (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i]: (v2_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.59/0.77      inference('sup+', [status(thm)], ['5', '21'])).
% 0.59/0.77  thf('23', plain, ($false), inference('demod', [status(thm)], ['4', '22'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
