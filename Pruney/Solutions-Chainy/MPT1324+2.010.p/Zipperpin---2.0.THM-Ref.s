%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1ZUbgM3uKd

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  278 ( 518 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X6 @ X5 ) ) @ ( k1_tops_2 @ X6 @ X5 @ X7 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X6 ) @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4
        = ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('10',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1ZUbgM3uKd
% 0.16/0.36  % Computer   : n021.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 18:30:50 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 12 iterations in 0.013s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.48  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.48  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.23/0.48  thf(t45_tops_2, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( l1_pre_topc @ A ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ![C:$i]:
% 0.23/0.48             ( ( m1_subset_1 @
% 0.23/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48               ( ( r1_tarski @
% 0.23/0.48                   B @ 
% 0.23/0.48                   ( k5_setfam_1 @
% 0.23/0.48                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.23/0.48                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.23/0.48                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( l1_pre_topc @ A ) =>
% 0.23/0.48          ( ![B:$i]:
% 0.23/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48              ( ![C:$i]:
% 0.23/0.48                ( ( m1_subset_1 @
% 0.23/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48                  ( ( r1_tarski @
% 0.23/0.48                      B @ 
% 0.23/0.48                      ( k5_setfam_1 @
% 0.23/0.48                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.23/0.48                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.23/0.48                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_C @ 
% 0.23/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t44_tops_2, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( l1_pre_topc @ A ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ![C:$i]:
% 0.23/0.48             ( ( m1_subset_1 @
% 0.23/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48               ( r1_tarski @
% 0.23/0.48                 ( k5_setfam_1 @
% 0.23/0.48                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.23/0.48                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.23/0.48                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.23/0.48          | (r1_tarski @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X6 @ X5)) @ 
% 0.23/0.48              (k1_tops_2 @ X6 @ X5 @ X7)) @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ X6) @ X7))
% 0.23/0.48          | ~ (m1_subset_1 @ X7 @ 
% 0.23/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.23/0.48          | ~ (l1_pre_topc @ X6))),
% 0.23/0.48      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (l1_pre_topc @ sk_A)
% 0.23/0.48          | (r1_tarski @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.23/0.48              (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.23/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('6', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((r1_tarski @ 
% 0.23/0.48           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.23/0.48            (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.23/0.48           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.23/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf('7', plain,
% 0.23/0.48      ((r1_tarski @ 
% 0.23/0.48        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.48         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.23/0.48        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '6'])).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      ((r1_tarski @ sk_B @ 
% 0.23/0.48        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.48         (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t45_xboole_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.23/0.48       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      (![X3 : $i, X4 : $i]:
% 0.23/0.48         (((X4) = (k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3)))
% 0.23/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.23/0.48      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (((k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.48         (k1_tops_2 @ sk_A @ sk_B @ sk_C))
% 0.23/0.48         = (k2_xboole_0 @ sk_B @ 
% 0.23/0.48            (k4_xboole_0 @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.48              (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.23/0.48             sk_B)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.48  thf(t11_xboole_1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.48         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.23/0.48  thf('12', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (r1_tarski @ 
% 0.23/0.48             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.48              (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.23/0.48             X0)
% 0.23/0.48          | (r1_tarski @ sk_B @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.48  thf('13', plain,
% 0.23/0.48      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.23/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.23/0.48  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
