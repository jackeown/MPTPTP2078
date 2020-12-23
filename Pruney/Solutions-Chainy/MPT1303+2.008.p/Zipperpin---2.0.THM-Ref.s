%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kNVEl2dhDe

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:19 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  319 ( 649 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_3 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X39 @ X37 @ X38 )
        = ( k3_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_3 )
      = ( k3_xboole_0 @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X33 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_3 )
      = ( k3_xboole_0 @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ( v1_tops_2 @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X49 )
      | ~ ( v1_tops_2 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C_3 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C_3 ) @ sk_A ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['4','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kNVEl2dhDe
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 1939 iterations in 0.892s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.35  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.13/1.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.13/1.35  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 1.13/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.35  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.13/1.35  thf(t21_tops_2, conjecture,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( l1_pre_topc @ A ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( m1_subset_1 @
% 1.13/1.35             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( m1_subset_1 @
% 1.13/1.35                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35               ( ( v1_tops_2 @ B @ A ) =>
% 1.13/1.35                 ( v1_tops_2 @
% 1.13/1.35                   ( k9_subset_1 @
% 1.13/1.35                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.13/1.35                   A ) ) ) ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i]:
% 1.13/1.35        ( ( l1_pre_topc @ A ) =>
% 1.13/1.35          ( ![B:$i]:
% 1.13/1.35            ( ( m1_subset_1 @
% 1.13/1.35                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35              ( ![C:$i]:
% 1.13/1.35                ( ( m1_subset_1 @
% 1.13/1.35                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35                  ( ( v1_tops_2 @ B @ A ) =>
% 1.13/1.35                    ( v1_tops_2 @
% 1.13/1.35                      ( k9_subset_1 @
% 1.13/1.35                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.13/1.35                      A ) ) ) ) ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 1.13/1.35  thf('0', plain,
% 1.13/1.35      (~ (v1_tops_2 @ 
% 1.13/1.35          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_3) @ 
% 1.13/1.35          sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_C_3 @ 
% 1.13/1.35        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(redefinition_k9_subset_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.35       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.13/1.35  thf('2', plain,
% 1.13/1.35      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.13/1.35         (((k9_subset_1 @ X39 @ X37 @ X38) = (k3_xboole_0 @ X37 @ X38))
% 1.13/1.35          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 1.13/1.35      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_3)
% 1.13/1.35           = (k3_xboole_0 @ X0 @ sk_C_3))),
% 1.13/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.13/1.35  thf('4', plain, (~ (v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C_3) @ sk_A)),
% 1.13/1.35      inference('demod', [status(thm)], ['0', '3'])).
% 1.13/1.35  thf(t48_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i]:
% 1.13/1.35         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.13/1.35           = (k3_xboole_0 @ X16 @ X17))),
% 1.13/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.13/1.35  thf(t36_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.35  thf('6', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.13/1.35      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.13/1.35  thf('7', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.13/1.35      inference('sup+', [status(thm)], ['5', '6'])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_B @ 
% 1.13/1.35        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('9', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_C_3 @ 
% 1.13/1.35        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(dt_k9_subset_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.35       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.13/1.35         ((m1_subset_1 @ (k9_subset_1 @ X33 @ X34 @ X35) @ (k1_zfmisc_1 @ X33))
% 1.13/1.35          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X33)))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.13/1.35  thf('11', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (m1_subset_1 @ 
% 1.13/1.35          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_3) @ 
% 1.13/1.35          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['9', '10'])).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_3)
% 1.13/1.35           = (k3_xboole_0 @ X0 @ sk_C_3))),
% 1.13/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.13/1.35  thf('13', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C_3) @ 
% 1.13/1.35          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('demod', [status(thm)], ['11', '12'])).
% 1.13/1.35  thf(t18_tops_2, axiom,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( l1_pre_topc @ A ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( m1_subset_1 @
% 1.13/1.35             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( m1_subset_1 @
% 1.13/1.35                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 1.13/1.35                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 1.13/1.35  thf('14', plain,
% 1.13/1.35      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X47 @ 
% 1.13/1.35             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 1.13/1.35          | (v1_tops_2 @ X47 @ X48)
% 1.13/1.35          | ~ (r1_tarski @ X47 @ X49)
% 1.13/1.35          | ~ (v1_tops_2 @ X49 @ X48)
% 1.13/1.35          | ~ (m1_subset_1 @ X49 @ 
% 1.13/1.35               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 1.13/1.35          | ~ (l1_pre_topc @ X48))),
% 1.13/1.35      inference('cnf', [status(esa)], [t18_tops_2])).
% 1.13/1.35  thf('15', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (l1_pre_topc @ sk_A)
% 1.13/1.35          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.35               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.13/1.35          | ~ (v1_tops_2 @ X1 @ sk_A)
% 1.13/1.35          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C_3) @ X1)
% 1.13/1.35          | (v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.35  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('17', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X1 @ 
% 1.13/1.35             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.13/1.35          | ~ (v1_tops_2 @ X1 @ sk_A)
% 1.13/1.35          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C_3) @ X1)
% 1.13/1.35          | (v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_A))),
% 1.13/1.35      inference('demod', [status(thm)], ['15', '16'])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_A)
% 1.13/1.35          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_B)
% 1.13/1.35          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['8', '17'])).
% 1.13/1.35  thf('19', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('20', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_A)
% 1.13/1.35          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C_3) @ sk_B))),
% 1.13/1.35      inference('demod', [status(thm)], ['18', '19'])).
% 1.13/1.35  thf('21', plain, ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C_3) @ sk_A)),
% 1.13/1.35      inference('sup-', [status(thm)], ['7', '20'])).
% 1.13/1.35  thf('22', plain, ($false), inference('demod', [status(thm)], ['4', '21'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.21/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
