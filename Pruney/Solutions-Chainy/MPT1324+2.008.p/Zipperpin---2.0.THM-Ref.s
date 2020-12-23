%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bYBtYpKdiU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  342 ( 582 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X11 @ X10 ) ) @ ( k1_tops_2 @ X11 @ X10 @ X12 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X11 ) @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bYBtYpKdiU
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:23:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 31 iterations in 0.018s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.47  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.47  thf(t45_tops_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( m1_subset_1 @
% 0.22/0.47                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47               ( ( r1_tarski @
% 0.22/0.47                   B @ 
% 0.22/0.47                   ( k5_setfam_1 @
% 0.22/0.47                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.47                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.22/0.47                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( l1_pre_topc @ A ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47              ( ![C:$i]:
% 0.22/0.47                ( ( m1_subset_1 @
% 0.22/0.47                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47                  ( ( r1_tarski @
% 0.22/0.47                      B @ 
% 0.22/0.47                      ( k5_setfam_1 @
% 0.22/0.47                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.47                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.22/0.47                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_C @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t44_tops_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( m1_subset_1 @
% 0.22/0.47                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47               ( r1_tarski @
% 0.22/0.47                 ( k5_setfam_1 @
% 0.22/0.47                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.22/0.47                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.22/0.47                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.47          | (r1_tarski @ 
% 0.22/0.47             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X11 @ X10)) @ 
% 0.22/0.47              (k1_tops_2 @ X11 @ X10 @ X12)) @ 
% 0.22/0.47             (k5_setfam_1 @ (u1_struct_0 @ X11) @ X12))
% 0.22/0.47          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.47               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.22/0.47          | ~ (l1_pre_topc @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ sk_A)
% 0.22/0.47          | (r1_tarski @ 
% 0.22/0.47             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.22/0.47              (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.22/0.47             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r1_tarski @ 
% 0.22/0.47           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.22/0.47            (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.22/0.47           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((r1_tarski @ 
% 0.22/0.47        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.47        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((r1_tarski @ sk_B @ 
% 0.22/0.47        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47         (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t3_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X4 : $i, X6 : $i]:
% 0.22/0.47         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ 
% 0.22/0.47        (k1_zfmisc_1 @ 
% 0.22/0.47         (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47          (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf(t2_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         ((r2_hidden @ X2 @ X3)
% 0.22/0.47          | (v1_xboole_0 @ X3)
% 0.22/0.47          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (((v1_xboole_0 @ 
% 0.22/0.47         (k1_zfmisc_1 @ 
% 0.22/0.47          (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47           (k1_tops_2 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.47        | (r2_hidden @ sk_B @ 
% 0.22/0.47           (k1_zfmisc_1 @ 
% 0.22/0.47            (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47             (k1_tops_2 @ sk_A @ sk_B @ sk_C)))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf(fc1_subset_1, axiom,
% 0.22/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.47  thf('13', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((r2_hidden @ sk_B @ 
% 0.22/0.47        (k1_zfmisc_1 @ 
% 0.22/0.47         (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47          (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.47      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(t99_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.22/0.47  thf('15', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.22/0.47  thf(t56_setfam_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.47       ( r1_tarski @ C @ B ) ))).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.47         (~ (r1_tarski @ (k3_tarski @ X7) @ X8)
% 0.22/0.47          | ~ (r2_hidden @ X9 @ X7)
% 0.22/0.47          | (r1_tarski @ X9 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.47          | (r1_tarski @ X2 @ X1)
% 0.22/0.47          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_B @ X0)
% 0.22/0.47          | ~ (r1_tarski @ 
% 0.22/0.47               (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.47                (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.47               X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '18'])).
% 0.22/0.47  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
