%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywf1wMSiFP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 ( 405 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

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

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( X6
       != ( u1_struct_0 @ X4 ) )
      | ~ ( v1_tex_2 @ X4 @ X5 )
      | ( v1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_tex_2 @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywf1wMSiFP
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 19 iterations in 0.015s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.19/0.46  thf(t15_tex_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_pre_topc @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.46           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.19/0.46                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_pre_topc @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.46              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.19/0.46                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.19/0.46  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t1_tsep_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_pre_topc @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.46           ( m1_subset_1 @
% 0.19/0.46             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (m1_pre_topc @ X2 @ X3)
% 0.19/0.46          | (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.19/0.46          | ~ (l1_pre_topc @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.46        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.19/0.46  thf('6', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t13_tex_2, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_pre_topc @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.19/0.46                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.19/0.46                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (m1_pre_topc @ X4 @ X5)
% 0.19/0.46          | ((X6) != (u1_struct_0 @ X4))
% 0.19/0.46          | ~ (v1_tex_2 @ X4 @ X5)
% 0.19/0.46          | (v1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.19/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.46          | ~ (l1_pre_topc @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         (~ (l1_pre_topc @ X5)
% 0.19/0.46          | ~ (m1_subset_1 @ (u1_struct_0 @ X4) @ 
% 0.19/0.46               (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.46          | (v1_subset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X5))
% 0.19/0.46          | ~ (v1_tex_2 @ X4 @ X5)
% 0.19/0.46          | ~ (m1_pre_topc @ X4 @ X5))),
% 0.19/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.46          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.19/0.46          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.19/0.46          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.46  thf('10', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.46          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.19/0.46          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.19/0.46        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.19/0.46        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '12'])).
% 0.19/0.46  thf('14', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.46  thf(fc14_subset_1, axiom,
% 0.19/0.46    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.19/0.46  thf('17', plain, (![X1 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X1) @ X1)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.19/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.46  thf('18', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.46  thf('19', plain, (![X1 : $i]: ~ (v1_subset_1 @ X1 @ X1)),
% 0.19/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain, ($false), inference('sup-', [status(thm)], ['16', '19'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
