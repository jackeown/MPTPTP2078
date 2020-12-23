%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ttptd63P94

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  480 (1286 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t36_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k2_pre_topc @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( ( k2_pre_topc @ X4 @ ( k4_subset_1 @ ( u1_struct_0 @ X4 ) @ X3 @ X5 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k2_pre_topc @ X4 @ X3 ) @ ( k2_pre_topc @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','12'])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_pre_topc @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
       != X6 )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
     != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
     != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ttptd63P94
% 0.13/0.37  % Computer   : n001.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:49:00 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 106 iterations in 0.094s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.54  thf(t36_tops_1, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.23/0.54                 ( v4_pre_topc @
% 0.23/0.54                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54              ( ![C:$i]:
% 0.23/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.23/0.54                    ( v4_pre_topc @
% 0.23/0.54                      ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t36_tops_1])).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t50_pre_topc, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54               ( ( k2_pre_topc @
% 0.23/0.54                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.23/0.54                 ( k4_subset_1 @
% 0.23/0.54                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.23/0.54                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.23/0.54          | ((k2_pre_topc @ X4 @ (k4_subset_1 @ (u1_struct_0 @ X4) @ X3 @ X5))
% 0.23/0.54              = (k4_subset_1 @ (u1_struct_0 @ X4) @ (k2_pre_topc @ X4 @ X3) @ 
% 0.23/0.54                 (k2_pre_topc @ X4 @ X5)))
% 0.23/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.23/0.54          | ~ (l1_pre_topc @ X4)
% 0.23/0.54          | ~ (v2_pre_topc @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [t50_pre_topc])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (v2_pre_topc @ sk_A)
% 0.23/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ((k2_pre_topc @ sk_A @ 
% 0.23/0.54              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.23/0.54              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.54                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ((k2_pre_topc @ sk_A @ 
% 0.23/0.54              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.23/0.54              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.54                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.23/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t52_pre_topc, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_pre_topc @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.23/0.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.23/0.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.23/0.54          | ~ (v4_pre_topc @ X6 @ X7)
% 0.23/0.54          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.23/0.54          | ~ (l1_pre_topc @ X7))),
% 0.23/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.54        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.23/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('11', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('12', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ((k2_pre_topc @ sk_A @ 
% 0.23/0.54              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.23/0.54              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.54                 (k2_pre_topc @ sk_A @ X0))))),
% 0.23/0.54      inference('demod', [status(thm)], ['6', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((k2_pre_topc @ sk_A @ 
% 0.23/0.54         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.54            (k2_pre_topc @ sk_A @ sk_C)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.23/0.54          | ~ (v4_pre_topc @ X6 @ X7)
% 0.23/0.54          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.23/0.54          | ~ (l1_pre_topc @ X7))),
% 0.23/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.54        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.23/0.54        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('20', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.23/0.54      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (((k2_pre_topc @ sk_A @ 
% 0.23/0.54         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.23/0.54      inference('demod', [status(thm)], ['14', '20'])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_k4_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.54       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 0.23/0.54          | (m1_subset_1 @ (k4_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.23/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.23/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.23/0.54          | ~ (v2_pre_topc @ X7)
% 0.23/0.54          | ((k2_pre_topc @ X7 @ X6) != (X6))
% 0.23/0.54          | (v4_pre_topc @ X6 @ X7)
% 0.23/0.54          | ~ (l1_pre_topc @ X7))),
% 0.23/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.54        | (v4_pre_topc @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.23/0.54           sk_A)
% 0.23/0.54        | ((k2_pre_topc @ sk_A @ 
% 0.23/0.54            (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54            != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54        | ~ (v2_pre_topc @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (((v4_pre_topc @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.23/0.54         sk_A)
% 0.23/0.54        | ((k2_pre_topc @ sk_A @ 
% 0.23/0.54            (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54            != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.23/0.54      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      (~ (v4_pre_topc @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.23/0.54          sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (((k2_pre_topc @ sk_A @ 
% 0.23/0.54         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.23/0.54         != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.23/0.54      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.54  thf('34', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['21', '33'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
