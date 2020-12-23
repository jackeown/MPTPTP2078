%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtXkqLzG8w

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:40 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  481 (1343 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) ) @ ( k1_tops_2 @ X14 @ X13 @ X15 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X14 ) @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X9 @ X8 ) )
        = X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ sk_B )
    | ( ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X11 @ X10 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('28',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','12','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtXkqLzG8w
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:30:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.66/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.87  % Solved by: fo/fo7.sh
% 0.66/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.87  % done 276 iterations in 0.431s
% 0.66/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.87  % SZS output start Refutation
% 0.66/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.87  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.66/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.87  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.66/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.87  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.66/0.87  thf(t45_tops_2, conjecture,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ![C:$i]:
% 0.66/0.87             ( ( m1_subset_1 @
% 0.66/0.87                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.87               ( ( r1_tarski @
% 0.66/0.87                   B @ 
% 0.66/0.87                   ( k5_setfam_1 @
% 0.66/0.87                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.66/0.87                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.66/0.87                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.66/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.87    (~( ![A:$i]:
% 0.66/0.87        ( ( l1_pre_topc @ A ) =>
% 0.66/0.87          ( ![B:$i]:
% 0.66/0.87            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87              ( ![C:$i]:
% 0.66/0.87                ( ( m1_subset_1 @
% 0.66/0.87                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.87                  ( ( r1_tarski @
% 0.66/0.87                      B @ 
% 0.66/0.87                      ( k5_setfam_1 @
% 0.66/0.87                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.66/0.87                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.66/0.87                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.66/0.87    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.66/0.87  thf('0', plain,
% 0.66/0.87      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('1', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('2', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ 
% 0.66/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(t44_tops_2, axiom,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ![C:$i]:
% 0.66/0.87             ( ( m1_subset_1 @
% 0.66/0.87                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.87               ( r1_tarski @
% 0.66/0.87                 ( k5_setfam_1 @
% 0.66/0.87                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.66/0.87                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.66/0.87                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.66/0.87  thf('3', plain,
% 0.66/0.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.66/0.87          | (r1_tarski @ 
% 0.66/0.87             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) @ 
% 0.66/0.87              (k1_tops_2 @ X14 @ X13 @ X15)) @ 
% 0.66/0.87             (k5_setfam_1 @ (u1_struct_0 @ X14) @ X15))
% 0.66/0.87          | ~ (m1_subset_1 @ X15 @ 
% 0.66/0.87               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.66/0.87          | ~ (l1_pre_topc @ X14))),
% 0.66/0.87      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.66/0.87  thf('4', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (l1_pre_topc @ sk_A)
% 0.66/0.87          | (r1_tarski @ 
% 0.66/0.87             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.66/0.87              (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.66/0.87             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.66/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.87  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('6', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((r1_tarski @ 
% 0.66/0.87           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.66/0.87            (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.66/0.87           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.66/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('demod', [status(thm)], ['4', '5'])).
% 0.66/0.87  thf('7', plain,
% 0.66/0.87      ((r1_tarski @ 
% 0.66/0.87        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.66/0.87         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.66/0.87        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.66/0.87      inference('sup-', [status(thm)], ['1', '6'])).
% 0.66/0.87  thf('8', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(t29_pre_topc, axiom,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.66/0.87  thf('9', plain,
% 0.66/0.87      (![X8 : $i, X9 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.66/0.87          | ((u1_struct_0 @ (k1_pre_topc @ X9 @ X8)) = (X8))
% 0.66/0.87          | ~ (l1_pre_topc @ X9))),
% 0.66/0.87      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.66/0.87  thf('10', plain,
% 0.66/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.87        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.66/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.87  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('12', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['10', '11'])).
% 0.66/0.87  thf('13', plain,
% 0.66/0.87      ((r1_tarski @ sk_B @ 
% 0.66/0.87        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.66/0.87         (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('14', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['10', '11'])).
% 0.66/0.87  thf('15', plain,
% 0.66/0.87      ((r1_tarski @ sk_B @ 
% 0.66/0.87        (k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.87  thf(d10_xboole_0, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.87  thf('16', plain,
% 0.66/0.87      (![X0 : $i, X2 : $i]:
% 0.66/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.87  thf('17', plain,
% 0.66/0.87      ((~ (r1_tarski @ 
% 0.66/0.87           (k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ sk_B)
% 0.66/0.87        | ((k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) = (sk_B)))),
% 0.66/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.87  thf('18', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('19', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ 
% 0.66/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(dt_k1_tops_2, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( ( l1_pre_topc @ A ) & 
% 0.66/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.66/0.87         ( m1_subset_1 @
% 0.66/0.87           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.66/0.87       ( m1_subset_1 @
% 0.66/0.87         ( k1_tops_2 @ A @ B @ C ) @ 
% 0.66/0.87         ( k1_zfmisc_1 @
% 0.66/0.87           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.66/0.87  thf('20', plain,
% 0.66/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.66/0.87          | ~ (l1_pre_topc @ X11)
% 0.66/0.87          | ~ (m1_subset_1 @ X12 @ 
% 0.66/0.87               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.66/0.87          | (m1_subset_1 @ (k1_tops_2 @ X11 @ X10 @ X12) @ 
% 0.66/0.87             (k1_zfmisc_1 @ 
% 0.66/0.87              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X11 @ X10))))))),
% 0.66/0.87      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 0.66/0.87  thf('21', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_C) @ 
% 0.66/0.87           (k1_zfmisc_1 @ 
% 0.66/0.87            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.66/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['19', '20'])).
% 0.66/0.87  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('23', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_C) @ 
% 0.66/0.87           (k1_zfmisc_1 @ 
% 0.66/0.87            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.66/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.87  thf('24', plain,
% 0.66/0.87      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ 
% 0.66/0.87        (k1_zfmisc_1 @ 
% 0.66/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['18', '23'])).
% 0.66/0.87  thf('25', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['10', '11'])).
% 0.66/0.87  thf('26', plain,
% 0.66/0.87      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ 
% 0.66/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.66/0.87      inference('demod', [status(thm)], ['24', '25'])).
% 0.66/0.87  thf(dt_k5_setfam_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.66/0.87       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.66/0.87  thf('27', plain,
% 0.66/0.87      (![X3 : $i, X4 : $i]:
% 0.66/0.87         ((m1_subset_1 @ (k5_setfam_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.66/0.87          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.66/0.87      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.66/0.87  thf('28', plain,
% 0.66/0.87      ((m1_subset_1 @ 
% 0.66/0.87        (k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.66/0.87        (k1_zfmisc_1 @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.87  thf(t3_subset, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.87  thf('29', plain,
% 0.66/0.87      (![X5 : $i, X6 : $i]:
% 0.66/0.87         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.87  thf('30', plain,
% 0.66/0.87      ((r1_tarski @ (k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.66/0.87        sk_B)),
% 0.66/0.87      inference('sup-', [status(thm)], ['28', '29'])).
% 0.66/0.87  thf('31', plain,
% 0.66/0.87      (((k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['17', '30'])).
% 0.66/0.87  thf('32', plain,
% 0.66/0.87      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['7', '12', '31'])).
% 0.66/0.87  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.66/0.87  
% 0.66/0.87  % SZS output end Refutation
% 0.66/0.87  
% 0.66/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
