%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G94LjTiyVX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 392 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t31_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G94LjTiyVX
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 335 iterations in 0.094s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(t31_tops_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @
% 0.20/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.55               ( m1_subset_1 @
% 0.20/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( l1_pre_topc @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( m1_subset_1 @
% 0.20/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.55                  ( m1_subset_1 @
% 0.20/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (~ (m1_subset_1 @ sk_C @ 
% 0.20/0.55          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k2_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('3', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('4', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t39_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.55               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.55          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.55          | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X1)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.55  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf(t79_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((r1_tarski @ (k1_zfmisc_1 @ X7) @ (k1_zfmisc_1 @ X8))
% 0.20/0.55          | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((r1_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf(t12_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55         = (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('19', plain, ((r1_tarski @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf(t10_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (r1_tarski @ sk_C @ 
% 0.20/0.55          (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X11 : $i, X13 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (m1_subset_1 @ sk_C @ 
% 0.20/0.55          (k1_zfmisc_1 @ 
% 0.20/0.55           (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (m1_subset_1 @ sk_C @ 
% 0.20/0.55          (k1_zfmisc_1 @ 
% 0.20/0.55           (k2_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)) @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['16', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['15', '24'])).
% 0.20/0.55  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
