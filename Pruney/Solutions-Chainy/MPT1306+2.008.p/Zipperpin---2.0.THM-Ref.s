%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B1yE8piGIY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  401 ( 768 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ~ ( v2_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X5 ) ) @ X4 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( r1_tarski @ X44 @ X42 )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

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

thf('22',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v2_tops_2 @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ~ ( v2_tops_2 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ X1 )
      | ( v2_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ X1 )
      | ( v2_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('28',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['6','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B1yE8piGIY
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 97 iterations in 0.065s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(t24_tops_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @
% 0.21/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52               ( ( v2_tops_2 @ B @ A ) =>
% 0.21/0.52                 ( v2_tops_2 @
% 0.21/0.52                   ( k9_subset_1 @
% 0.21/0.52                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.21/0.52                   A ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( l1_pre_topc @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @
% 0.21/0.52                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @
% 0.21/0.52                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52                  ( ( v2_tops_2 @ B @ A ) =>
% 0.21/0.52                    ( v2_tops_2 @
% 0.21/0.52                      ( k9_subset_1 @
% 0.21/0.52                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.21/0.52                      A ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (v2_tops_2 @ 
% 0.21/0.52          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.21/0.52          sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         (((k9_subset_1 @ X35 @ X33 @ X34) = (k3_xboole_0 @ X33 @ X34))
% 0.21/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.52  thf(t12_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         (((k9_subset_1 @ X35 @ X33 @ X34)
% 0.21/0.52            = (k1_setfam_1 @ (k2_tarski @ X33 @ X34)))
% 0.21/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.21/0.52           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (~ (v2_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.52  thf(t108_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.52          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X5)) @ X4))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t3_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @
% 0.21/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( r1_tarski @ C @ B ) =>
% 0.21/0.52               ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X42 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.21/0.52          | (m1_subset_1 @ X44 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.21/0.52          | ~ (r1_tarski @ X44 @ X42)
% 0.21/0.52          | ~ (l1_struct_0 @ X43))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_tops_2])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ sk_A)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_pre_topc @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '20'])).
% 0.21/0.52  thf(t19_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @
% 0.21/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.21/0.52                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X39 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.21/0.52          | (v2_tops_2 @ X39 @ X40)
% 0.21/0.52          | ~ (r1_tarski @ X39 @ X41)
% 0.21/0.52          | ~ (v2_tops_2 @ X41 @ X40)
% 0.21/0.52          | ~ (m1_subset_1 @ X41 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.21/0.52          | ~ (l1_pre_topc @ X40))),
% 0.21/0.52      inference('cnf', [status(esa)], [t19_tops_2])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.21/0.52          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ X1)
% 0.21/0.52          | (v2_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.21/0.52          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ X1)
% 0.21/0.52          | (v2_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)
% 0.21/0.52          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_B)
% 0.21/0.52          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.52  thf('28', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i]: (v2_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.52  thf('30', plain, ($false), inference('demod', [status(thm)], ['6', '29'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
