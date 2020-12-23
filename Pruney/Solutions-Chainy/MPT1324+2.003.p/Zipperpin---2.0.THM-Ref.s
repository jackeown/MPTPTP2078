%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYLrONCRlG

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:40 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  497 (1059 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) ) @ ( k1_tops_2 @ X10 @ X9 @ X11 ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ X10 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ( r1_tarski @ X6 @ ( sk_D @ X8 @ X7 @ X6 ) )
      | ( X7
        = ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( sk_D @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ~ ( r1_tarski @ X7 @ ( sk_D @ X8 @ X7 @ X6 ) )
      | ( X7
        = ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('14',plain,
    ( ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('17',plain,
    ( ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k2_xboole_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYLrONCRlG
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 442 iterations in 0.370s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.60/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.60/0.82  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.60/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(t45_tops_2, conjecture,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( l1_pre_topc @ A ) =>
% 0.60/0.82       ( ![B:$i]:
% 0.60/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.82           ( ![C:$i]:
% 0.60/0.82             ( ( m1_subset_1 @
% 0.60/0.82                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.82               ( ( r1_tarski @
% 0.60/0.82                   B @ 
% 0.60/0.82                   ( k5_setfam_1 @
% 0.60/0.82                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.60/0.82                     ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.60/0.82                 ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i]:
% 0.60/0.82        ( ( l1_pre_topc @ A ) =>
% 0.60/0.82          ( ![B:$i]:
% 0.60/0.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.82              ( ![C:$i]:
% 0.60/0.82                ( ( m1_subset_1 @
% 0.60/0.82                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.82                  ( ( r1_tarski @
% 0.60/0.82                      B @ 
% 0.60/0.82                      ( k5_setfam_1 @
% 0.60/0.82                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.60/0.82                        ( k1_tops_2 @ A @ B @ C ) ) ) =>
% 0.60/0.82                    ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t45_tops_2])).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      (~ (r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('1', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_C @ 
% 0.60/0.82        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t44_tops_2, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( l1_pre_topc @ A ) =>
% 0.60/0.82       ( ![B:$i]:
% 0.60/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.82           ( ![C:$i]:
% 0.60/0.82             ( ( m1_subset_1 @
% 0.60/0.82                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.82               ( r1_tarski @
% 0.60/0.82                 ( k5_setfam_1 @
% 0.60/0.82                   ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.60/0.82                   ( k1_tops_2 @ A @ B @ C ) ) @ 
% 0.60/0.82                 ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ))).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.60/0.82          | (r1_tarski @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X10 @ X9)) @ 
% 0.60/0.82              (k1_tops_2 @ X10 @ X9 @ X11)) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ X10) @ X11))
% 0.60/0.82          | ~ (m1_subset_1 @ X11 @ 
% 0.60/0.82               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.60/0.82          | ~ (l1_pre_topc @ X10))),
% 0.60/0.82      inference('cnf', [status(esa)], [t44_tops_2])).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (l1_pre_topc @ sk_A)
% 0.60/0.82          | (r1_tarski @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.60/0.82              (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.60/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.82  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_tarski @ 
% 0.60/0.82           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 0.60/0.82            (k1_tops_2 @ sk_A @ X0 @ sk_C)) @ 
% 0.60/0.82           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.60/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.82      inference('demod', [status(thm)], ['4', '5'])).
% 0.60/0.82  thf('7', plain,
% 0.60/0.82      ((r1_tarski @ 
% 0.60/0.82        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.82        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '6'])).
% 0.60/0.82  thf(d10_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.82  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.82      inference('simplify', [status(thm)], ['8'])).
% 0.60/0.82  thf(t14_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.60/0.82         ( ![D:$i]:
% 0.60/0.82           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.60/0.82             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.60/0.82       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X6 @ X7)
% 0.60/0.82          | ~ (r1_tarski @ X8 @ X7)
% 0.60/0.82          | (r1_tarski @ X6 @ (sk_D @ X8 @ X7 @ X6))
% 0.60/0.82          | ((X7) = (k2_xboole_0 @ X6 @ X8)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 0.60/0.82          | (r1_tarski @ X0 @ (sk_D @ X1 @ X0 @ X0))
% 0.60/0.82          | ~ (r1_tarski @ X1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (((r1_tarski @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82         (sk_D @ 
% 0.60/0.82          (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82           (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.82          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.60/0.82        | ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82            = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82               (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82                (k1_tops_2 @ sk_A @ sk_B @ sk_C)))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '11'])).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X6 @ X7)
% 0.60/0.82          | ~ (r1_tarski @ X8 @ X7)
% 0.60/0.82          | ~ (r1_tarski @ X7 @ (sk_D @ X8 @ X7 @ X6))
% 0.60/0.82          | ((X7) = (k2_xboole_0 @ X6 @ X8)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      ((((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82          = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82              (k1_tops_2 @ sk_A @ sk_B @ sk_C))))
% 0.60/0.82        | ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82            = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82               (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82                (k1_tops_2 @ sk_A @ sk_B @ sk_C))))
% 0.60/0.82        | ~ (r1_tarski @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82              (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.60/0.82        | ~ (r1_tarski @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      ((r1_tarski @ 
% 0.60/0.82        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82         (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.82        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '6'])).
% 0.60/0.82  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.82      inference('simplify', [status(thm)], ['8'])).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      ((((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82          = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82              (k1_tops_2 @ sk_A @ sk_B @ sk_C))))
% 0.60/0.82        | ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82            = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82               (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82                (k1_tops_2 @ sk_A @ sk_B @ sk_C)))))),
% 0.60/0.82      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.60/0.82         = (k2_xboole_0 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.60/0.82            (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82             (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 0.60/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      ((r1_tarski @ sk_B @ 
% 0.60/0.82        (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82         (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t10_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (r1_tarski @ sk_B @ 
% 0.60/0.82          (k2_xboole_0 @ X0 @ 
% 0.60/0.82           (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.60/0.82            (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.82  thf('22', plain,
% 0.60/0.82      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.60/0.82      inference('sup+', [status(thm)], ['18', '21'])).
% 0.60/0.82  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
