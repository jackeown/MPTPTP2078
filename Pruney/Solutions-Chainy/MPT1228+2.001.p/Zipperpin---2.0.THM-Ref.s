%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ZXW3FpKzw

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  248 ( 680 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t37_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_tops_1])).

thf('0',plain,(
    ~ ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['6','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ZXW3FpKzw
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 15 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(t37_tops_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.46                 ( v3_pre_topc @
% 0.20/0.46                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46              ( ![C:$i]:
% 0.20/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                  ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.46                    ( v3_pre_topc @
% 0.20/0.46                      ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t37_tops_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (~ (v3_pre_topc @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.46          sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 0.20/0.46          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.46            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.46         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.46  thf('6', plain, (~ (v3_pre_topc @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(fc7_tops_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.46         ( v3_pre_topc @ C @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.46          | ~ (v3_pre_topc @ X3 @ X4)
% 0.20/0.46          | ~ (l1_pre_topc @ X4)
% 0.20/0.46          | ~ (v2_pre_topc @ X4)
% 0.20/0.46          | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.46          | (v3_pre_topc @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc7_tops_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v3_pre_topc @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.46          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v3_pre_topc @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.46        | (v3_pre_topc @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.46  thf('16', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('17', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain, ($false), inference('demod', [status(thm)], ['6', '17'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
