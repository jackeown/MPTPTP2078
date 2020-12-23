%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WelwfQNfyn

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  298 ( 538 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ~ ( r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) ) @ ( k1_tops_2 @ X10 @ X9 @ X11 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X10 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C_1 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C_1 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WelwfQNfyn
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 38 iterations in 0.046s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.50  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t45_tops_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @
% 0.21/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50               ( ( r1_tarski @
% 0.21/0.50                   B @ 
% 0.21/0.50                   ( k5_setfam_1 @
% 0.21/0.50                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.21/0.50                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.21/0.50                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_pre_topc @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @
% 0.21/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50                  ( ( r1_tarski @
% 0.21/0.50                      B @ 
% 0.21/0.50                      ( k5_setfam_1 @
% 0.21/0.50                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.21/0.50                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.21/0.50                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t44_tops_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @
% 0.21/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50               ( r1_tarski @
% 0.21/0.50                 ( k5_setfam_1 @
% 0.21/0.50                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.21/0.50                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.21/0.50                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X10 @ X9)) @ 
% 0.21/0.50              (k1_tops_2 @ X10 @ X9 @ X11)) @ 
% 0.21/0.50             (k5_setfam_1 @ (u1_struct_0 @ X10) @ X11))
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.50          | ~ (l1_pre_topc @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.21/0.50              (k1_tops_2 @ sk_A @ X0 @ sk_C_1)) @ 
% 0.21/0.50             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ 
% 0.21/0.50           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.21/0.50            (k1_tops_2 @ sk_A @ X0 @ sk_C_1)) @ 
% 0.21/0.50           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((r1_tarski @ 
% 0.21/0.50        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.21/0.50         (k1_tops_2 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((r1_tarski @ sk_B @ 
% 0.21/0.50        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.21/0.50         (k1_tops_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((r2_hidden @ sk_B @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.21/0.50          (k1_tops_2 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.50  thf(t99_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.50  thf('12', plain, (![X5 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X5)) = (X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.50  thf(t56_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.50       ( r1_tarski @ C @ B ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.21/0.50          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.50          | (r1_tarski @ X8 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.50          | (r1_tarski @ X2 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ sk_B @ X0)
% 0.21/0.50          | ~ (r1_tarski @ 
% 0.21/0.50               (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.21/0.50                (k1_tops_2 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50               X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '15'])).
% 0.21/0.50  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
