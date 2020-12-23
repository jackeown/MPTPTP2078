%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pKJ5YKFrlT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 303 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t15_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ~ ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ A ) )
                & ( v1_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tex_2])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( X5
       != ( u1_struct_0 @ X3 ) )
      | ( v1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('16',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ X2 @ X2 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    $false ),
    inference('sup-',[status(thm)],['13','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pKJ5YKFrlT
% 0.16/0.37  % Computer   : n001.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:20:15 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 15 iterations in 0.012s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(dt_k2_subset_1, axiom,
% 0.24/0.50    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.24/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.24/0.50  thf('1', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.50  thf('2', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(t15_tex_2, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( l1_pre_topc @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.50           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.24/0.50                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( l1_pre_topc @ A ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.50              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.24/0.50                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.24/0.50  thf('3', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(d3_tex_2, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( l1_pre_topc @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.50           ( ( v1_tex_2 @ B @ A ) <=>
% 0.24/0.50             ( ![C:$i]:
% 0.24/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.50                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.24/0.50                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.50         (~ (m1_pre_topc @ X3 @ X4)
% 0.24/0.50          | ~ (v1_tex_2 @ X3 @ X4)
% 0.24/0.50          | ((X5) != (u1_struct_0 @ X3))
% 0.24/0.50          | (v1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.24/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.50          | ~ (l1_pre_topc @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         (~ (l1_pre_topc @ X4)
% 0.24/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X3) @ 
% 0.24/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.50          | (v1_subset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.24/0.50          | ~ (v1_tex_2 @ X3 @ X4)
% 0.24/0.50          | ~ (m1_pre_topc @ X3 @ X4))),
% 0.24/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.24/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.24/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.50          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.24/0.50          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.24/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '5'])).
% 0.24/0.50  thf('7', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.24/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.24/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.50          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.24/0.50          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.24/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.24/0.50        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.24/0.50        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.24/0.50  thf('11', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('12', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.24/0.50  thf(fc14_subset_1, axiom,
% 0.24/0.50    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.24/0.50  thf('14', plain, (![X2 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X2) @ X2)),
% 0.24/0.50      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.24/0.50  thf('15', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.50  thf('16', plain, (![X2 : $i]: ~ (v1_subset_1 @ X2 @ X2)),
% 0.24/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.50  thf('17', plain, ($false), inference('sup-', [status(thm)], ['13', '16'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
