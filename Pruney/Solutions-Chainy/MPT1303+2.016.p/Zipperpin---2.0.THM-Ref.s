%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v8q6PE4nso

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:20 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 700 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k9_subset_1 @ X35 @ X33 @ X34 )
        = ( k3_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k9_subset_1 @ X35 @ X33 @ X34 )
        = ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( r1_tarski @ X44 @ X42 )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

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

thf('20',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v1_tops_2 @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ~ ( v1_tops_2 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['9','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['6','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v8q6PE4nso
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 135 iterations in 0.101s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(t21_tops_2, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @
% 0.38/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @
% 0.38/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56               ( ( v1_tops_2 @ B @ A ) =>
% 0.38/0.56                 ( v1_tops_2 @
% 0.38/0.56                   ( k9_subset_1 @
% 0.38/0.56                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.38/0.56                   A ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( l1_pre_topc @ A ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( m1_subset_1 @
% 0.38/0.56                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( m1_subset_1 @
% 0.38/0.56                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56                  ( ( v1_tops_2 @ B @ A ) =>
% 0.38/0.56                    ( v1_tops_2 @
% 0.38/0.56                      ( k9_subset_1 @
% 0.38/0.56                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.38/0.56                      A ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (~ (v1_tops_2 @ 
% 0.38/0.56          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.38/0.56          sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         (((k9_subset_1 @ X35 @ X33 @ X34) = (k3_xboole_0 @ X33 @ X34))
% 0.38/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.56  thf(t12_setfam_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X36 : $i, X37 : $i]:
% 0.38/0.56         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         (((k9_subset_1 @ X35 @ X33 @ X34)
% 0.38/0.56            = (k1_setfam_1 @ (k2_tarski @ X33 @ X34)))
% 0.38/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.38/0.56           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (~ (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '5'])).
% 0.38/0.56  thf(t48_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.38/0.56           = (k3_xboole_0 @ X4 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X36 : $i, X37 : $i]:
% 0.38/0.56         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.38/0.56           = (k1_setfam_1 @ (k2_tarski @ X4 @ X5)))),
% 0.38/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t36_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.38/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t3_tops_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_struct_0 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @
% 0.38/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( r1_tarski @ C @ B ) =>
% 0.38/0.56               ( m1_subset_1 @
% 0.38/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X42 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.38/0.56          | (m1_subset_1 @ X44 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.38/0.56          | ~ (r1_tarski @ X44 @ X42)
% 0.38/0.56          | ~ (l1_struct_0 @ X43))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_tops_2])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ sk_A)
% 0.38/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.38/0.56          | (m1_subset_1 @ X0 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_l1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_pre_topc @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X0 @ sk_B)
% 0.38/0.56          | (m1_subset_1 @ X0 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.38/0.56          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '18'])).
% 0.38/0.56  thf(t18_tops_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @
% 0.38/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @
% 0.38/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.38/0.56                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X39 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.38/0.56          | (v1_tops_2 @ X39 @ X40)
% 0.38/0.56          | ~ (r1_tarski @ X39 @ X41)
% 0.38/0.56          | ~ (v1_tops_2 @ X41 @ X40)
% 0.38/0.56          | ~ (m1_subset_1 @ X41 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.38/0.56          | ~ (l1_pre_topc @ X40))),
% 0.38/0.56      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.56          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.38/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.56          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.38/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.38/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.38/0.56          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.38/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.56  thf('26', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i]: (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)),
% 0.38/0.56      inference('sup+', [status(thm)], ['9', '27'])).
% 0.38/0.56  thf('29', plain, ($false), inference('demod', [status(thm)], ['6', '28'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
