%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLnnlU7hsx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  62 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  242 ( 542 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
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

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_subset_1 @ X6 @ X5 )
      | ( X6 != X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('7',plain,(
    ! [X5: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( v1_subset_1 @ X5 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('10',plain,
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

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( v1_tex_2 @ X2 @ X3 )
      | ( X4
       != ( u1_struct_0 @ X2 ) )
      | ( v1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_tex_2 @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['8','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLnnlU7hsx
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 16 iterations in 0.012s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(t15_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.48                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_pre_topc @ A ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.48                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.22/0.48  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t1_tsep_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( m1_subset_1 @
% 0.22/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.48          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.48          | ~ (l1_pre_topc @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.48  thf(d7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (v1_subset_1 @ X6 @ X5)
% 0.22/0.48          | ((X6) != (X5))
% 0.22/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X5 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5)) | ~ (v1_subset_1 @ X5 @ X5))),
% 0.22/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.48  thf('10', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d3_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.48             ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X2 @ X3)
% 0.22/0.48          | ~ (v1_tex_2 @ X2 @ X3)
% 0.22/0.48          | ((X4) != (u1_struct_0 @ X2))
% 0.22/0.48          | (v1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.22/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.48          | ~ (l1_pre_topc @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X3)
% 0.22/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.22/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X3))
% 0.22/0.48          | ~ (v1_tex_2 @ X2 @ X3)
% 0.22/0.48          | ~ (m1_pre_topc @ X2 @ X3))),
% 0.22/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.48  thf('14', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.22/0.48        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.22/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.48  thf('18', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.48  thf('21', plain, ($false), inference('demod', [status(thm)], ['8', '20'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
